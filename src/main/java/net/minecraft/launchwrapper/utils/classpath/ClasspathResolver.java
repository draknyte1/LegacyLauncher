package net.minecraft.launchwrapper.utils.classpath;

import java.net.URL;

public interface ClasspathResolver {
    URL[] resolve(ClassLoader loader) throws Throwable;
}