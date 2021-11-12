package net.minecraft.launchwrapper;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.JarURLConnection;
import java.net.URL;
import java.net.URLClassLoader;
import java.net.URLConnection;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.CodeSigner;
import java.security.CodeSource;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.jar.Attributes;
import java.util.jar.Attributes.Name;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.Manifest;

import javax.annotation.Nullable;

import org.apache.logging.log4j.Level;

public class LaunchClassLoader extends URLClassLoader {

	static {
		/* Use this, if you encounter weird issues */
		if(Boolean.parseBoolean(System.getProperty("legacy.parallelClassLoader", "true"))) {
			LogWrapper.fine("Registering LaunchClassLoader as parallel capable");
			ClassLoader.registerAsParallelCapable();
		}
	}

	public static final int BUFFER_SIZE = 1 << 12;
	private List<URL> sources;
	private ClassLoader parent = getClass().getClassLoader();

	private List<IClassTransformer> transformers = new ArrayList<IClassTransformer>(2);
	private Map<String, Class<?>> cachedClasses = new ConcurrentHashMap<String, Class<?>>();
	private Set<String> invalidClasses = new HashSet<String>(1000);

	private Set<String> classLoaderExceptions = new HashSet<String>();
	private Set<String> transformerExceptions = new HashSet<String>();
	private Map<String,byte[]> resourceCache = new ConcurrentHashMap<String,byte[]>(1000);
	private Set<String> negativeResourceCache = Collections.newSetFromMap(new ConcurrentHashMap<String, Boolean>());

	private IClassNameTransformer renameTransformer;

	private final ThreadLocal<byte[]> loadBuffer = ThreadLocal.withInitial(() -> new byte[BUFFER_SIZE]);

	private static final String[] RESERVED_NAMES = {"CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9"};

	private static final boolean DEBUG = Boolean.parseBoolean(System.getProperty("legacy.debugClassLoading", "false"));
	private static final boolean DEBUG_FINER = DEBUG && Boolean.parseBoolean(System.getProperty("legacy.debugClassLoadingFiner", "false"));
	private static final boolean DEBUG_SAVE = DEBUG && Boolean.parseBoolean(System.getProperty("legacy.debugClassLoadingSave", "false"));
	private static final Path DUMP_PATH = Paths.get(System.getProperty("legacy.classDumpPath", "./.classloader.out"));
	private static File tempFolder = null;

	public LaunchClassLoader(URL[] sources) {
		super(sources, null);
		this.sources = new ArrayList<URL>(Arrays.asList(sources));

		// classloader exclusions
		getClassLoaderExclusions().addAll(Arrays.asList(
				"java.",
				"jdk.",
				"sun.",
				"org.lwjgl.",
				"org.apache.logging.",
				"net.minecraft.launchwrapper."
				));

		// transformer exclusions
		getTransformerExclusions().addAll(Arrays.asList(
				"javax.",
				"jdk.",
				"argo.",
				"org.objectweb.asm.",
				"com.google.common.",
				"org.bouncycastle."
				));

		// See: https://github.com/SpongePowered/SpongeCommon/commit/8f284427ca50d445d0fffab4afc8251388ada8e9
		/*
		 * By default Launchwrapper inherits the class path from the system class loader.
		 * However, JRE extensions (e.g. Nashorn in the jre/lib/ext directory) are not part
		 * of the class path of the system class loader.
		 * Instead, they're loaded using a parent class loader (Launcher.ExtClassLoader).
		 * Currently, Launchwrapper does not fall back to the parent class loader if it's
		 * unable to find a class on its class path. To make the JRE extensions usable for
		 * plugins we manually add the URLs from the ExtClassLoader to Launchwrapper's
		 * class path.
		 */
		ClassLoader classLoader = ClassLoader.getSystemClassLoader();
		if (classLoader == null) {
			return;
		}

		classLoader = classLoader.getParent(); // Launcher.ExtClassLoader
		if (classLoader instanceof URLClassLoader) {
			for (URL url : ((URLClassLoader) classLoader).getURLs()) {
				addURL(url);
			}
		}

		if (DEBUG_SAVE) {
			int x = 1;
			tempFolder = new File(Launch.minecraftHome, "CLASSLOADER_TEMP");
			while (tempFolder.exists() && x <= 10) {
				tempFolder = new File(Launch.minecraftHome, "CLASSLOADER_TEMP" + x++);
			}

			if (tempFolder.exists()) {
				LogWrapper.info("DEBUG_SAVE enabled, but 10 temp directories already exist, clean them and try again.");
				tempFolder = null;
			} else {
				LogWrapper.info("DEBUG_SAVE Enabled, saving all classes to \"%s\"", tempFolder.getAbsolutePath().replace('\\', '/'));
				tempFolder.mkdirs();
			}
		}
	}

	/**
	 * Registers transformer class
	 *
	 * @param transformerClassName Fully qualified transformer class name, see {@link Class#getName()}
	 */
	public void registerTransformer( String transformerClassName) {
		try {
			IClassTransformer transformer = (IClassTransformer) loadClass(transformerClassName).newInstance();
			transformers.add(transformer);
			if (transformer instanceof IClassNameTransformer && renameTransformer == null) {
				renameTransformer = (IClassNameTransformer) transformer;
			}
		} catch (Exception e) {
			LogWrapper.log(Level.ERROR, "A critical problem occurred registering the transformer class {}", transformerClassName, e);
		}
	}

	@Override
	public Class<?> findClass(final String name) throws ClassNotFoundException {
		if(invalidClasses.contains(name)) {
			throw new ClassNotFoundException(name);
		}

		for(final String exception : classLoaderExceptions) {
			if(name.startsWith(exception))
				return parent.loadClass(name);
		}

		if(cachedClasses.containsKey(name))
			return cachedClasses.get(name);

		for(final String exception : transformerExceptions) {
			if(name.startsWith(exception)) {
				try {
					final Class<?> clazz = super.findClass(name);
					cachedClasses.put(name, clazz);
					return clazz;
				} catch (ClassNotFoundException e) {
					invalidClasses.add(name);
					throw e;
				}
			}
		}

		final String transformedName = transformName(name);
		if(cachedClasses.containsKey(transformedName)) {
			return cachedClasses.get(transformedName);
		}

		final String untransformedName = untransformName(name);

		// Get class bytes
		byte[] classData = getClassBytes(untransformedName);

		byte[] transformedClass = null;
		try {
			// Run transformers (running with null class bytes is valid, because transformers may generate classes dynamically)
			transformedClass = runTransformers(untransformedName, transformedName, classData);
		} catch (Exception e) {
			if(DEBUG)
				LogWrapper.trace("Exception encountered while transformimg class {}", name, e);
		}

		// If transformer chain provides no class data, mark given class name invalid and throw CNFE
		if(transformedClass == null) {
			invalidClasses.add(name);
			throw new ClassNotFoundException(name);
		}

		// Save class if requested so
		if(DEBUG_SAVE) {
			try {
				saveTransformedClass(transformedClass, transformedName);
			} catch(Exception e){
				LogWrapper.warning("Failed to save class {}", transformedName, e);
				e.printStackTrace();
			}
		}

		// Define package for class
		int lastDot = untransformedName.lastIndexOf('.');
		String packageName = lastDot == -1 ? "" : untransformedName.substring(0, lastDot);
		String fileName = untransformedName.replace('.', '/').concat(".class");
		URLConnection urlConnection = findCodeSourceConnectionFor(fileName);
		CodeSigner[] signers = null;

		try {
			if (lastDot > -1 && !untransformedName.startsWith("net.minecraft.")) {
				if (urlConnection instanceof JarURLConnection) {
					final JarURLConnection jarURLConnection = (JarURLConnection) urlConnection;
					final JarFile jarFile = jarURLConnection.getJarFile();

					if (jarFile != null && jarFile.getManifest() != null) {
						final Manifest manifest = jarFile.getManifest();
						final JarEntry entry = jarFile.getJarEntry(fileName);

						Package pkg = getPackage(packageName);
						getClassBytes(untransformedName);
						signers = entry.getCodeSigners();
						if (pkg == null) {
							pkg = definePackage(packageName, manifest, jarURLConnection.getJarFileURL());
						} else {
							if (pkg.isSealed() && !pkg.isSealed(jarURLConnection.getJarFileURL())) {
								LogWrapper.severe("The jar file {} is trying to seal already secured path {}", jarFile.getName(), packageName);
							} else if (isSealed(packageName, manifest)) {
								LogWrapper.severe("The jar file {} has a security seal for path {}, but that path is defined and not secure", jarFile.getName(), packageName);
							}
						}
					}
				} else {
					Package pkg = getPackage(packageName);
					if (pkg == null) {
						pkg = definePackage(packageName, null, null, null, null, null, null, null);
					} else if (pkg.isSealed()) {
						URL url = urlConnection != null ? urlConnection.getURL() : null;
						LogWrapper.severe("The URL {} is defining elements for sealed path {}", url, packageName);
					}
				}
			}

			// Define class
			final CodeSource codeSource = urlConnection == null ? null : new CodeSource(urlConnection.getURL(), signers);
			final Class<?> clazz = defineClass(transformedName, transformedClass, 0, transformedClass.length, codeSource);
			cachedClasses.put(transformedName, clazz);
			return clazz;
		} catch (Exception e) {
			invalidClasses.add(name);
			if (DEBUG) {
				LogWrapper.trace("Exception encountered attempting classloading of {}", name, e);
			}
			throw new ClassNotFoundException(name, e);
		}
	}


	private void saveTransformedClass(final byte[] data, final String transformedName) {
		if (tempFolder == null || transformedName == null || data == null) {
			return;
		}

		final File outFile = new File(tempFolder, transformedName.replace('.', File.separatorChar) + ".class");
		final File outDir = outFile.getParentFile();

		if (!outDir.exists()) {
			outDir.mkdirs();
		}

		if (outFile.exists()) {
			outFile.delete();
		}

		try {
			LogWrapper.fine("Saving transformed class \"%s\" to \"%s\"", transformedName, outFile.getAbsolutePath().replace('\\', '/'));

			final OutputStream output = new FileOutputStream(outFile);
			output.write(data);
			output.close();
		} catch (IOException ex) {
			LogWrapper.log(Level.WARN, ex, "Could not save transformed class \"%s\"", transformedName);
		}
	}

	private String untransformName(final String name) {
		if (renameTransformer != null) {
			return renameTransformer.unmapClassName(name);
		}

		return name;
	}

	private String transformName(final String name) {
		if (renameTransformer != null) {
			return renameTransformer.remapClassName(name);
		}

		return name;
	}

	private boolean isSealed(final String path, final Manifest manifest) {
		Attributes attributes = manifest.getAttributes(path);
		String sealed = null;
		if (attributes != null) {
			sealed = attributes.getValue(Name.SEALED);
		}

		if (sealed == null) {
			attributes = manifest.getMainAttributes();
			if (attributes != null) {
				sealed = attributes.getValue(Name.SEALED);
			}
		}
		return "true".equalsIgnoreCase(sealed);
	}

	private URLConnection findCodeSourceConnectionFor(final String name) {
		final URL resource = findResource(name);
		if (resource != null) {
			try {
				return resource.openConnection();
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}

		return null;
	}

	private byte[] runTransformers(String name, String transformedName, @Nullable byte[] basicClass) {
		if(DEBUG_FINER)
			LogWrapper.finest("Beginning transform of {{} ({})} Start Length: {}", name, transformedName, basicClass != null ? basicClass.length : 0);

		for (final IClassTransformer transformer : transformers) {
			final String transName = transformer.getClass().getName();

			if(DEBUG_FINER)
				LogWrapper.finest("Before Transformer {{} ({})} {}: {}", name, transformedName, transName, basicClass != null ? basicClass.length : 0);

			basicClass = transformer.transform(name, transformedName, basicClass);

			if(DEBUG_FINER)
				LogWrapper.finest("After  Transformer {{} ({})} {}: {}", name, transformedName, transName, basicClass != null ? basicClass.length : 0);
		}
		return basicClass;
	}

	@Override
	public void addURL(final URL url) {
		super.addURL(url);
		sources.add(url);
	}

	public List<URL> getSources() {
		return sources;
	}

	private byte[] readFully(InputStream stream) {
		try(ByteArrayOutputStream os = new ByteArrayOutputStream(stream.available())) {
			int readBytes;
			byte[] buffer = loadBuffer.get();

			while ((readBytes = stream.read(buffer, 0, buffer.length)) != -1)
				os.write(buffer, 0, readBytes);

			return os.toByteArray();
		} catch (Throwable t) {
			LogWrapper.warning("Problem reading stream fully", t);
			return null;
		}
	}

	/**
	 * Gets list of registered {@link IClassTransformer} instances
	 *
	 * @return List of registered {@link IClassTransformer} instances
	 */
	public List<IClassTransformer> getTransformers() {
		return Collections.unmodifiableList(transformers);
	}

	/**
	 * Adds classloader exclusion. Fully qualified class names starting with {@code toExclude} will be loaded
	 * from parent classloader
	 *
	 * @param toExclude Part of fully qualified class name
	 * @deprecated Use {@link #getClassLoaderExclusions()} instead
	 */
	@Deprecated
	public void addClassLoaderExclusion(String toExclude) {
		classLoaderExceptions.add(toExclude);
	}

	/**
	 * Gets a {@link Set} of classloader exclusions.
	 *
	 * Classlaoder exclusions look like this: {@code com.mojang.authlib.}, so that means all classes and subclasses
	 * in {@code com.mojang.authlib} class would be loaded from parent classloader
	 *
	 * @return {@link Set} of classloader exclusions
	 */
	public Set<String> getClassLoaderExclusions() {
		return classLoaderExceptions;
	}

	/**
	 * Adds transformer exclusion. Given classes won't be transformed by {@link IClassTransformer}s
	 *
	 * @param toExclude Part of fully qualified class name
	 * @see #getTransformers() For list of registered transformers
	 * @deprecated Use {@link #getTransformerExclusions()} instead.
	 */
	@Deprecated
	public void addTransformerExclusion(String toExclude) {
		transformerExceptions.add(toExclude);
	}

	/**
	 * Gets a {@link Set} of transformer exclusions.
	 *
	 * Transformer exclusions look like this: {@code com.mojang.authlib.}, so that means all classes and subclasses
	 * in {@code com.mojang.authlib} class won't be transformed
	 *
	 * @return {@link Set} of transformer exclusions.
	 */
	public Set<String> getTransformerExclusions() {
		return transformerExceptions;
	}

	/**`
	 * Gets class raw bytes
	 *
	 * @param name Class name
	 * @return Class raw bytes, or null if class was not found
	 */
	@Nullable
	public byte[] getClassBytes(String name) {
		if (negativeResourceCache.contains(name)) {
			return null;
		} else if (resourceCache.containsKey(name)) {
			return resourceCache.get(name);
		}
		if (name.indexOf('.') == -1) {
			for (final String reservedName : RESERVED_NAMES) {
				if (name.toUpperCase(Locale.ENGLISH).startsWith(reservedName)) {
					final byte[] data = getClassBytes("_" + name);
					if (data != null) {
						resourceCache.put(name, data);
						return data;
					}
				}
			}
		}

		String resourcePath = name.replace('.', '/').concat(".class");
		URL classResource = findResource(resourcePath);
		if (classResource == null) {
			if (DEBUG) {
				LogWrapper.trace("Failed to find class resource {}", resourcePath);
			}
			negativeResourceCache.add(name);
			return null;
		}
		try(InputStream classStream = classResource.openStream()) {
			if (DEBUG) {
				LogWrapper.trace("Loading class {} from resource {}", name, classResource.toString());
			}
			byte[] data = Objects.requireNonNull(readFully(classStream));
			resourceCache.put(name, data);
			return data;
		} 
		catch (Exception e) {
			if(DEBUG) {
				LogWrapper.trace("Failed to load class {} from resource {}", name, classResource.toString());
			}
			negativeResourceCache.add(name);
			return null;
		}
	}

	public void clearNegativeEntries(Set<String> entriesToClear) {
		negativeResourceCache.removeAll(entriesToClear);
	}
}
