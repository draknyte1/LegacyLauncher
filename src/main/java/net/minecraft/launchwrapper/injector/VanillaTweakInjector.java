package net.minecraft.launchwrapper.injector;

import static org.objectweb.asm.Opcodes.ACC_STATIC;
import static org.objectweb.asm.Opcodes.INVOKESTATIC;
import static org.objectweb.asm.Opcodes.PUTSTATIC;

import java.awt.Frame;
import java.awt.Image;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import javax.imageio.ImageIO;

import org.lwjgl.opengl.Display;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Label;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.ClassNode;
import org.objectweb.asm.tree.FieldNode;
import org.objectweb.asm.tree.MethodNode;

import net.minecraft.launch.MinecraftLaunchHelper;
import net.minecraft.launchwrapper.IClassTransformer;
import net.minecraft.launchwrapper.Launch;

public class VanillaTweakInjector implements IClassTransformer {
    public VanillaTweakInjector() {
    }

    @Override
    public byte[] transform(final String name, final String transformedName, final byte[] bytes) {
        if (bytes == null) {
            return null;
        }
        if (!MinecraftLaunchHelper.getMinecraftMainClass().equals(name)) {
            return bytes;
        }

        final ClassNode classNode = new ClassNode();
        final ClassReader classReader = new ClassReader(bytes);
        classReader.accept(classNode, ClassReader.EXPAND_FRAMES);

        MethodNode mainMethod = null;
        for (final MethodNode methodNode : classNode.methods) {
            if ("main".equals(methodNode.name)) {
                mainMethod = methodNode;
                break;
            }
        }
        if (mainMethod == null) {
            // WTF? We got no main method
            return bytes;
        }

        FieldNode workDirNode = null;
        for (final FieldNode fieldNode : classNode.fields) {
            final String fileTypeDescriptor = Type.getDescriptor(File.class);
            if (fileTypeDescriptor.equals(fieldNode.desc) && (fieldNode.access & ACC_STATIC) == ACC_STATIC) {
                workDirNode = fieldNode;
                break;
            }
        }

        // Prepare our injection code
        final MethodNode injectedMethod = new MethodNode();
        final Label label = new Label();
        injectedMethod.visitLabel(label);
        injectedMethod.visitLineNumber(9001, label); // Linenumber which shows up in the stacktrace
        // Call the method below
        injectedMethod.visitMethodInsn(INVOKESTATIC, "net/minecraft/launchwrapper/injector/VanillaTweakInjector", "inject", "()Ljava/io/File;", false);
        // Store the result in the workDir variable.
        injectedMethod.visitFieldInsn(PUTSTATIC, "net/minecraft/client/Minecraft", Objects.requireNonNull(workDirNode).name, "Ljava/io/File;");

        mainMethod.instructions.insert(injectedMethod.instructions);

        final ClassWriter writer = new ClassWriter(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES);
        classNode.accept(writer);
        return writer.toByteArray();
    }

    public static File inject() {
        // Speed up imageloading
        System.out.println("Turning off ImageIO disk-caching");
        ImageIO.setUseCache(false);

        loadIconsOnFrames();

        // Set the workdir, return value will get assigned
        System.out.println("Setting gameDir to: " + Launch.minecraftHome);
        return Launch.minecraftHome;
    }

    public static void loadIconsOnFrames() {
        try {
            // Load icon from disk
            final File smallIcon = new File(Launch.assetsDir, "icons/icon_16x16.png");
            final File bigIcon = new File(Launch.assetsDir, "icons/icon_32x32.png");
            System.out.println("Attempting to load current icons for window from: " + smallIcon + " and " + bigIcon);
            Display.setIcon(new ByteBuffer[]{
                    loadIcon(smallIcon),
                    loadIcon(bigIcon)
            });
            Frame[] frames = Frame.getFrames();

            if (frames.length != 0) {
                final List<Image> icons = Arrays.<Image>asList(ImageIO.read(smallIcon), ImageIO.read(bigIcon));

                for (Frame frame : frames) {
                    try {
                        frame.setIconImages(icons);
                    } catch (Throwable throwable) {
                        throwable.printStackTrace();
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static ByteBuffer loadIcon(final File iconFile) throws IOException {
        final BufferedImage icon = ImageIO.read(iconFile);

        final int[] rgb = icon.getRGB(0, 0, icon.getWidth(), icon.getHeight(), null, 0, icon.getWidth());

        final ByteBuffer buffer = ByteBuffer.allocate(4 * rgb.length);
        for (int color : rgb) {
            buffer.putInt(color << 8 | ((color >> 24) & 0xFF));
        }
        buffer.flip();
        return buffer;
    }
}
