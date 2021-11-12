package net.minecraft.launchwrapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.Reader;
import java.net.JarURLConnection;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.net.URLConnection;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.security.CodeSigner;
import java.security.CodeSource;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.jar.JarFile;
import java.util.zip.Adler32;

import javax.annotation.Nullable;

import org.apache.logging.log4j.Level;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import net.minecraft.launchwrapper.utils.classes.CachedClassInfo;
import net.minecraft.launchwrapper.utils.mixin.MixinSupport;

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
	private static final Gson GSON = new GsonBuilder().create();

	private List<IClassTransformer> transformers = new ArrayList<IClassTransformer>(2);
	private Map<String, Class<?>> cachedClasses = new ConcurrentHashMap<String, Class<?>>();
	private List<IResourceTransformer> resourceTransformers = new ArrayList<>();
	private Map<String, byte[]> cachedResources = new ConcurrentHashMap<>();
	private Set<String> invalidClasses = new HashSet<String>(1000);

	private FileSystem cacheFileSystem;
	private CachedClassInfo cachedClassInfo;

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
	private boolean isMixinLoaded = false;

	public LaunchClassLoader(URL[] sources) {
		super(sources, null);
		this.sources = new ArrayList<URL>(Arrays.asList(sources));

		// classloader exclusions
		getClassLoaderExclusions().addAll(Arrays.asList(
				"java.",
				"jdk.",
				"sun.",
				"com.sun.",
				"org.lwjgl.",
				"org.apache.logging.",
				"net.minecraft.launchwrapper."
				));

		// transformer exclusions
		getTransformerExclusions().addAll(Arrays.asList(
				"java.",
				"javax.",
				"jdk.",
				"sun.",
				"com.sun.",
				"argo.",
				"org.objectweb.asm.",
				"com.google.common.",
				"org.bouncycastle."
				));

		// Init class cache
		initializeClassCacheSystem();		

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
		if (classLoader != null) {
			classLoader = classLoader.getParent(); // Launcher.ExtClassLoader
			if (classLoader instanceof URLClassLoader) {
				for (URL url : ((URLClassLoader) classLoader).getURLs()) {
					addURL(url);
				}
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
				if(!tempFolder.mkdirs()) {
					LogWrapper.severe("Can't create temp directories!");
				}
			}
		}
	}

	private void initializeClassCacheSystem() {
		long startTime = System.nanoTime();

		File classCachesZip = new File(Launch.minecraftHome, "class_cache.zip");
		Map<String, String> env = new HashMap<String, String>();
		env.put("create", "true");
		try {
			URI classCachesURI = classCachesZip.toURI(); // here
			URI classCachesZipURI = new URI("jar:" + classCachesURI.getScheme(), classCachesURI.getPath(), null);
			cacheFileSystem = FileSystems.newFileSystem(classCachesZipURI, env, null);
		} catch (Throwable t) {
			if (classCachesZip.exists()) {
				LogWrapper.severe("Failed to read class caches", t);
				try {
					classCachesZip.delete();
					URI classCachesURI = classCachesZip.toURI(); // here
					URI classCahcesZipURI = new URI("jar:" + classCachesURI.getScheme(), classCachesURI.getPath(), null);
					cacheFileSystem = FileSystems.newFileSystem(classCahcesZipURI, env, null);
				} catch (Exception e) {
					throw new RuntimeException("Could not create cached_classes.zip", e);
				}
			} else {
				throw t instanceof RuntimeException ? (RuntimeException) t : new RuntimeException("Could not create cached_classes.zip", t);
			}
		}

		Path classInfoCacheFile = cacheFileSystem.getPath("cached_class_info.json");

		long result;
		try {
			Adler32 adler32 = new Adler32();

			File modsFolder = new File(Launch.minecraftHome, "mods");
			if (modsFolder.exists()) {
				for (File modFile : modsFolder.listFiles()) {
					if (modFile.isFile()) {
						adler32.update(Files.readAllBytes(modFile.toPath()));
					}
				}

				result = adler32.getValue();
			} else {
				result = 0;
			}
		} catch (IOException e1) {
			throw new RuntimeException(e1);
		}
		long modsHash = result;

		try {
			if (Files.exists(classInfoCacheFile)) {
				try (Reader reader = new InputStreamReader(Files.newInputStream(classInfoCacheFile))) {
					cachedClassInfo = GSON.fromJson(reader, CachedClassInfo.class);
				}

				if (modsHash != cachedClassInfo.modsHash) {
					LogWrapper.info("Mods hash changed, creating new cache: " + modsHash + " != " + cachedClassInfo.modsHash);
					cachedClassInfo = null;
				}
			}
		} catch (Throwable t) {
			LogWrapper.severe("Failed to read cached_class_info.json", t);
		}

		if (cachedClassInfo == null) {
			cachedClassInfo = new CachedClassInfo();
			cachedClassInfo.modsHash = modsHash;
		}

		Runtime.getRuntime().addShutdownHook(new Thread(() -> {
			// TODO: Doesn't always log message, log4j shutdown hook needs to run after this one
			try {
				Files.write(classInfoCacheFile, GSON.toJson(cachedClassInfo).getBytes(), StandardOpenOption.CREATE);
				cacheFileSystem.close();
				LogWrapper.info("Saved caches successfully");
			} catch (Throwable t) {
				LogWrapper.severe("Failed to save caches", t);
			}
		}));

		LogWrapper.info("Initialized cache system in {} ns", System.nanoTime() - startTime);
	}

	/**
	 * Registers transformer class
	 *
	 * @param transformerClassName Fully qualified transformer class name, see {@link Class#getName()}.
	 */
	public void registerTransformer( String transformerClassName) {
		try {
			IClassTransformer transformer = (IClassTransformer) loadClass(transformerClassName).newInstance();
			transformers.add(transformer);
			if (transformer instanceof IClassNameTransformer/* && renameTransformer == null*/) {
				renameTransformer = (IClassNameTransformer) transformer;
			}
		} catch (Exception e) {
			LogWrapper.severe("A critical problem occurred registering the transformer class {}", transformerClassName, e);
		}
	}

	/**
	 * Registers transformer class
	 *
	 * @param transformerInstance Instance of pre-existing {@link IClassTransformer}.
	 */	
	public void registerTransformer(IClassTransformer transformerInstance) {
		try {
			transformers.add(transformerInstance);

			if (transformerInstance instanceof IClassNameTransformer)
				renameTransformer = (IClassNameTransformer) transformerInstance;
		} catch (Exception e) {
			LogWrapper.severe("A critical problem occurred registering the transformer class {}", transformerInstance.getClass().getName(), e);
		}
	}

	/**
	 * Registers resource transformer class
	 *
	 * @param transformerClassName Fully qualified transformer class name, see {@link Class#getName()}
	 */
	public void registerResourceTransformer(String className) {
		try {
			IResourceTransformer transformer = (IResourceTransformer) loadClass(className).newInstance();
			resourceTransformers.add(transformer);
		} catch (Exception e) {
			LogWrapper.severe("A critical problem occurred registering the resource transformer class {}", className, e);
		}
	}

	@Override
	public Class<?> findClass(final String name) throws ClassNotFoundException {
		if(invalidClasses.contains(name)) {
			throw new ClassNotFoundException(name);
		}

		// Check for mixins
		if (name.equals("org.spongepowered.asm.mixin.transformer.Proxy")) {
			isMixinLoaded = true;
		}

		for(final String exception : classLoaderExceptions) {
			if(name.startsWith(exception))
				return parent.loadClass(name);
		}

		if(cachedClasses.containsKey(name)) {
			return cachedClasses.get(name);
		}

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

		try {

			String transformedName = cachedClassInfo.transformedClassNames.get(name);
			if (transformedName == null) {
				transformedName = transformName(name);
				cachedClassInfo.transformedClassNames.put(name, transformedName);
			}
			String untransformedName = cachedClassInfo.untransformedClassNames.get(name);
			if (untransformedName == null) {
				untransformedName = untransformName(name);
				cachedClassInfo.untransformedClassNames.put(name, untransformedName);
			}
			final String fileName = untransformedName.replace('.', '/').concat(".class");
			URLConnection urlConnection = findCodeSourceConnectionFor(fileName);

			// Get class bytes
			byte[] untransformedClass = getClassBytes(untransformedName);

			// Get signers
			CodeSigner[] signers = null;
			if (untransformedName.indexOf('.') > -1 && !untransformedName.startsWith("net.minecraft.")) {
				if (urlConnection instanceof JarURLConnection) {
					final JarFile jarFile = ((JarURLConnection) urlConnection).getJarFile();
					if (jarFile != null && jarFile.getManifest() != null) {
						signers = jarFile.getJarEntry(fileName).getCodeSigners();
					}
				}
			}


			if (untransformedClass == null) {
				byte[] transformedClass = runTransformers(untransformedName, transformedName, untransformedClass);
				CodeSource codeSource = urlConnection == null ? null : new CodeSource(urlConnection.getURL(), signers);
				Class<?> clazz = defineClass(transformedName, transformedClass, 0, transformedClass.length, codeSource);
				cachedClasses.put(transformedName, clazz);
				return clazz;
			}

			// Calculate untransformed class hash
			Adler32 adler32 = new Adler32();
			adler32.update(untransformedClass);
			long untransformedClassHash = adler32.getValue();

			// Try getting the class from cache
			byte[] transformedClass = null;
			long transformedClassHash = cachedClassInfo.transformedClassHashes.getOrDefault(untransformedClassHash, 0L);

			if (transformedClassHash != 0) {
				try {
					if (transformedClassHash == untransformedClassHash) {
						transformedClass = untransformedClass;
					} else {
						transformedClass = getFromCache(transformedClassHash);
					}
					if (isMixinLoaded) {
						MixinSupport.onCachedClassLoad();
					}
				} catch (Throwable t) {
					LogWrapper.severe("Failed to read cached class {}", name, t);
				}
			}

			// Transform the class
			if (transformedClass == null) {			
				try {
					// Run transformers (running with null class bytes is valid, because transformers may generate classes dynamically)
					transformedClass = runTransformers(untransformedName, transformedName, untransformedClass);
				} catch (Exception e) {
					if(DEBUG)
						LogWrapper.trace("Exception encountered while transformimg class {}", name, e);
				}

				// Calculate transformed class hash
				adler32.reset();
				adler32.update(transformedClass);
				transformedClassHash = adler32.getValue();

				try {
					// Cache the transformed class
					if (transformedClassHash != untransformedClassHash) {
						saveToCache(transformedClassHash, transformedClass);
					}
					cachedClassInfo.transformedClassHashes.put(untransformedClassHash, transformedClassHash);
				} catch (Throwable t) {
					LogWrapper.severe("Failed to saving class to cache {}", name, t);
				}
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

			// Define class
			final CodeSource codeSource = urlConnection == null ? null : new CodeSource(urlConnection.getURL(), signers);
			final Class<?> clazz = defineClass(transformedName, transformedClass, 0, transformedClass.length, codeSource);
			cachedClasses.put(transformedName, clazz);
			return clazz;
		} 
		catch (Exception e) {
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
			if(!outDir.mkdirs()) {
				LogWrapper.severe("Can't create directories!");
			}
		}

		if (outFile.exists()) {
			if(!outFile.delete()) {
				LogWrapper.severe("Can't delete file!");
			}
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
		if(DEBUG_FINER) {
			LogWrapper.finest("Beginning transform of {{} ({})} Start Length: {}", name, transformedName, basicClass != null ? basicClass.length : 0);
		}

		for (final IClassTransformer transformer : transformers) {
			final String transName = transformer.getClass().getName();
			if(DEBUG_FINER) {
				LogWrapper.finest("Before Transformer {{} ({})} {}: {}", name, transformedName, transName, basicClass != null ? basicClass.length : 0);
			}
			basicClass = transformer.transform(name, transformedName, basicClass);
			if(DEBUG_FINER) {
				LogWrapper.finest("After  Transformer {{} ({})} {}: {}", name, transformedName, transName, basicClass != null ? basicClass.length : 0);
			}
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
			while ((readBytes = stream.read(buffer, 0, buffer.length)) != -1) {
				os.write(buffer, 0, readBytes);
			}
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
	 * Gets class raw bytes from ClassCache
	 *
	 * @param hash Class hash
	 * @return Class raw bytes, or null if class was not found
	 */
	private byte[] getFromCache(long hash) throws IOException {
		return Files.readAllBytes(cacheFileSystem.getPath(Long.toHexString(hash)));
	}

	/**`
	 * Saves class raw bytes to ClassCache
	 *
	 * @param hash Class hash
	 * @param data Class raw bytes
	 */
	private void saveToCache(long hash, byte[] data) throws IOException {
		Path path = cacheFileSystem.getPath(Long.toHexString(hash));

		if (!Files.exists(path)) {
			Files.write(path, data);
		}
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

	@Override
	public InputStream getResourceAsStream(String name) {
		if (resourceCache.containsKey(name)) {
			return new ByteArrayInputStream(resourceCache.get(name));
		}
		InputStream stream = super.getResourceAsStream(name);
		byte[] original = stream == null ? null : this.readFully(stream);
		byte[] transformed = null;
		for (IResourceTransformer transformer : resourceTransformers) {
			if ((transformed = transformer.transform(name, original)) != null) {
				resourceCache.put(name, transformed);
			}
		}
		if (transformed != null) {
			return new ByteArrayInputStream(transformed);
		}
		return super.getResourceAsStream(name);
	}

}
