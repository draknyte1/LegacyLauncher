package net.minecraft.launchwrapper.utils.classpath;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

public class Classpath {
    private static final List<ClasspathResolver> resolvers = new ArrayList<>();

    public static URL[] getClasspath() {
        ClassLoader classLoader = Classpath.class.getClassLoader();
        if (resolvers.isEmpty()) {
            // Backup time
            addResolver(new Java8ClasspathResolver());
            addResolver(new UnsafeClasspathResolver());
            addResolver(new PropertyClasspathResolver());
            addResolver(new HackyClasspathResolver());
        }

        for (ClasspathResolver resolver : resolvers) {
            try {
                return resolver.resolve(classLoader);
            } catch (Throwable ignored) {

            }
        }

        throw new IllegalStateException("Could not fetch the classpath (All the resolvers failed)");
    }

    public static void addResolver(ClasspathResolver resolver) {
        resolvers.add(resolver);
    }

    public static List<ClasspathResolver> getResolvers() {
        return resolvers;
    }
}