package net.minecraft.launchwrapper.utils.classpath;

import java.net.URL;
import java.net.URLClassLoader;

public class Java8ClasspathResolver implements ClasspathResolver {
    @Override
    public URL[] resolve(ClassLoader loader) throws Throwable {
        if (loader instanceof URLClassLoader) {
            return ((URLClassLoader) loader).getURLs();
        }

        throw new Exception();
    }
}