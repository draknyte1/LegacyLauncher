package net.minecraft.launch;

import org.spongepowered.asm.util.Constants;

public class MinecraftLaunchHelper {
	
    public static String getMinecraftMainClass() {
        return System.getProperty("net.minecraft.client.Minecraft");
    }
    
    public static String getMinecraftGameClass() {
        return System.getProperty("minecraft.launch.game"); // TODO
    }

    public static String getMixinSide() {
        return System.getProperty("minecraft.launch.mixin.side", Constants.SIDE_UNKNOWN); // TODO
    }
}