package net.minecraft.launchwrapper;

import java.io.File;
import java.lang.reflect.Method;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.Level;

import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;
import net.minecraft.launchwrapper.protocol.LegacyProtocolURLStreamHandlerFactory;
import net.minecraft.launchwrapper.utils.classpath.Classpath;

public class Launch {
	
	private static final String DEFAULT_TWEAK = "net.minecraft.launchwrapper.VanillaTweaker";
	/**
     * The game dir of Minecraft.
     */
	public static File minecraftHome;
	/**
     * The asset dir of Minecraft.
     */
	public static File assetsDir;
	/**
     * A map that contains information that tweakers can access.
     */
	public static Map<String, Object> blackboard;

	public static void main(String[] args) {
		System.out.println("Loading Debug LaunchWrapper (J9-17 Support & Misc Fixes.)");
		new Launch().launch(args);
	}
	
	/**
     * The class loader to register transformers to.
     */
	public static LaunchClassLoader classLoader;

	private Launch() {
		URL.setURLStreamHandlerFactory(new LegacyProtocolURLStreamHandlerFactory());

		// Try fancy hack
		classLoader = new LaunchClassLoader(Classpath.getClasspath());		
		
		blackboard = new HashMap<String, Object>();
		Thread.currentThread().setContextClassLoader(classLoader);
	}

	private void launch(String[] args) {
		final OptionParser parser = new OptionParser();
		parser.allowsUnrecognizedOptions();

		final OptionSpec<String> profileOption = parser.accepts("version", "The version we launched with").withRequiredArg();
		final OptionSpec<File> gameDirOption = parser.accepts("gameDir", "Alternative game directory").withRequiredArg().ofType(File.class);
		final OptionSpec<File> assetsDirOption = parser.accepts("assetsDir", "Assets directory").withRequiredArg().ofType(File.class);
		final OptionSpec<String> tweakClassOption = parser.accepts("tweakClass", "Tweak class(es) to load").withRequiredArg().defaultsTo(DEFAULT_TWEAK);
		final OptionSpec<String> nonOption = parser.nonOptions();

		final OptionSet options = parser.parse(args);
		minecraftHome = options.valueOf(gameDirOption);
		assetsDir = options.valueOf(assetsDirOption);
		final String profileName = options.valueOf(profileOption);
		final List<String> tweakClassNames = new ArrayList<String>(options.valuesOf(tweakClassOption));

		final List<String> argumentList = new ArrayList<String>();
		// This list of names will be interacted with through tweakers. They can append to this list
		// any 'discovered' tweakers from their preferred mod loading mechanism
		// By making this object discoverable and accessible it's possible to perform
		// things like cascading of tweakers
		blackboard.put("TweakClasses", tweakClassNames);

		// This argument list will be constructed from all tweakers. It is visible here so
		// all tweakers can figure out if a particular argument is present, and add it if not
		blackboard.put("ArgumentList", argumentList);

		// This is to prevent duplicates - in case a tweaker decides to add itself or something
		final Set<String> allTweakerNames = new HashSet<String>();
		// The 'definitive' list of tweakers
		final List<ITweaker> allTweakers = new ArrayList<ITweaker>();
		try {
			final List<ITweaker> tweakers = new ArrayList<ITweaker>(tweakClassNames.size() + 1);
			// The list of tweak instances - may be useful for interoperability
			blackboard.put("Tweaks", tweakers);
			// The primary tweaker (the first one specified on the command line) will actually
			// be responsible for providing the 'main' name and generally gets called first
			ITweaker primaryTweaker = null;
			// This loop will terminate, unless there is some sort of pathological tweaker
			// that reinserts itself with a new identity every pass
			// It is here to allow tweakers to "push" new tweak classes onto the 'stack' of
			// tweakers to evaluate allowing for cascaded discovery and injection of tweakers
			do {
				for (final Iterator<String> it = tweakClassNames.iterator(); it.hasNext(); ) {
					final String tweakName = it.next();
					// Safety check - don't reprocess something we've already visited
					if (allTweakerNames.contains(tweakName)) {
						LogWrapper.warning("Tweak class name {} has already been visited -- skipping", tweakName);
						// remove the tweaker from the stack otherwise it will create an infinite loop
						it.remove();
						continue;
					} else {
						allTweakerNames.add(tweakName);
					}
					LogWrapper.info("Loading tweak class name {}", tweakName);

					// Ensure we allow the tweak class to load with the parent classloader
					//classLoader.addClassLoaderExclusion(tweakName.substring(0, tweakName.lastIndexOf('.'))); // TODO
					classLoader.getClassLoaderExclusions().add(tweakName.substring(0, tweakName.lastIndexOf('.')));
					//final ITweaker tweaker = (ITweaker) Class.forName(tweakName, true, classLoader).newInstance(); // TODO
					final ITweaker tweaker = (ITweaker) Class.forName(tweakName, true, classLoader).getConstructor().newInstance();
					tweakers.add(tweaker);

					// Remove the tweaker from the list of tweaker names we've processed this pass
					it.remove();
					// If we haven't visited a tweaker yet, the first will become the 'primary' tweaker
					if (primaryTweaker == null) {
						LogWrapper.info("Using primary tweak class name {}", tweakName);
						primaryTweaker = tweaker;
					}
				}

				// Now, iterate all the tweakers we just instantiated
				while(!tweakers.isEmpty()) {
					// remove from the list once we've processed it, so we don't get duplicates	
                    final ITweaker tweaker = tweakers.remove(0);
					LogWrapper.info("Calling tweak class {}", tweaker.getClass().getName());
					tweaker.acceptOptions(options.valuesOf(nonOption), minecraftHome, assetsDir, profileName);
					tweaker.injectIntoClassLoader(classLoader);
					allTweakers.add(tweaker);				
				}
				// continue around the loop until there's no tweak classes
			} while (!tweakClassNames.isEmpty());

			// Once we're done, we then ask all the tweakers for their arguments and add them all to the
			// master argument list
			for (final ITweaker tweaker : allTweakers) {
				argumentList.addAll(Arrays.asList(tweaker.getLaunchArguments()));
			}
			
			// Tweak arguments as required.
			for (final ITweaker tweaker : allTweakers) {
                if (tweaker instanceof IArgumentTweaker)
                    ((IArgumentTweaker) tweaker).modifyArguments(argumentList);
            }

			// Finally we turn to the primary tweaker, and let it tell us where to go to launch
			final String launchTarget = primaryTweaker.getLaunchTarget();
			final Class<?> clazz = Class.forName(launchTarget, false, classLoader);
			final Method mainMethod = clazz.getMethod("main", new Class[]{String[].class});

			LogWrapper.info("Launching wrapped minecraft {{}}", launchTarget);
			mainMethod.invoke(null, (Object) argumentList.toArray(new String[argumentList.size()]));
		} catch (Exception e) {
			LogWrapper.log(Level.ERROR, e, "Unable to launch");
			throw new IllegalStateException("Unable to launch", e);
		}
	}
}
