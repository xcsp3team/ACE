/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package utility;

import static utility.Kit.control;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Stream;

import interfaces.Tags.TagExperimental;

/**
 * This class allows performing some operations based on reflection.
 * 
 * @author Christophe Lecoutre
 */
public class Reflector {

	public final static char JAR_SEPARATOR_CHAR = '/';

	// need to synchronize access to this structure ?
	private final static Map<String, String> mapOfClassNames = Collections.synchronizedMap(new HashMap<String, String>());

	/**
	 * Returns the last but one super class of the specified class
	 * 
	 * @param clazz
	 *            a class
	 * @return the last but one super class of the specified class
	 */
	public static Class<?> getLastButOneSuperclassOf(Class<?> clazz) {
		for (Class<?> superclass = clazz.getSuperclass(); superclass != Object.class; superclass = superclass.getSuperclass())
			clazz = superclass;
		return clazz;
	}

	/**
	 * Replaces all occurrences of the given old char with the given new char. This method is used as the standard
	 * method of the String class do not behave correctly for some characters.
	 */
	private static String replaceAll(String s, char oldChar, char newChar) {
		StringBuilder sb = new StringBuilder(s);
		for (int i = 0; i < sb.length(); i++)
			if (sb.charAt(i) == oldChar)
				sb.setCharAt(i, newChar);
		return sb.toString();
	}

	/**
	 * Returns the absolute name of the specified class (without the extension .class) with respect to the specified
	 * package name. Hence, this name starts with the given package name (and not with the root of a file system).
	 * 
	 * @param classFile
	 *            a File denoting a class.
	 * @param basicPackageName
	 *            a package name
	 * @return the absolute name of the specified class
	 */
	private static String absoluteClassNameOf(File classFile, String basicPackageName) {
		String s = replaceAll(classFile.getAbsolutePath(), File.separatorChar, '.');
		int firstIndex = s.indexOf(basicPackageName);
		assert firstIndex != -1;
		int lastIndex = s.lastIndexOf(".");
		return s.substring(firstIndex, lastIndex);
	}

	/**
	 * Returns the name of the field for the specified second object in the specified first object, or null
	 * 
	 * @param parentObject
	 *            an object
	 * @param fieldObject
	 *            a field to be looked for in the object
	 * @return the name of the field for the specified second object in the specified first object, or null
	 */
	public static String findFieldName(Object parentObject, Object fieldObject) {
		for (Field field : parentObject.getClass().getDeclaredFields()) {
			field.setAccessible(true);
			try {
				if (field.get(parentObject) == fieldObject)
					return field.getName();
			} catch (Exception e) {
				throw new AssertionError();
			}
		}
		return null;
	}

	private static void updateListIfSubclassing(List<Class<?>> list, Class<?> rootClass, String absoluteClassName, int requiredModifiers,
			int forbiddenModifiers) {
		try {
			Class<?> c = Class.forName(absoluteClassName);
			if ((c.getModifiers() & requiredModifiers) == requiredModifiers && (c.getModifiers() & forbiddenModifiers) == 0 && rootClass.isAssignableFrom(c)
					&& !TagExperimental.class.isAssignableFrom(c))
				list.add(c);
		} catch (ClassNotFoundException e) {
			(e.getCause() == null ? e : e.getCause()).printStackTrace();
		}
	}

	/**
	 * Returns a list of all (not abstract) classes which inherit from the given root class and which can be found from
	 * the given directory.
	 * 
	 * @param rootClass
	 *            a given class
	 * @param directory
	 *            a given directory
	 * @param requiredModifiers
	 *            a propagationSet of required modifiers for all subclasses
	 * @param forbiddenModifiers
	 *            a propagationSet of forbidden modifiers for all subclasses
	 */
	public static List<Class<?>> searchClassesInheritingFromIn(Class<?> rootClass, File directory, int requiredModifiers, int forbiddenModifiers) {
		assert directory.isDirectory();
		List<Class<?>> list = new ArrayList<>();
		for (File file : directory.listFiles()) {
			if (file.isDirectory())
				list.addAll(searchClassesInheritingFromIn(rootClass, file, requiredModifiers, forbiddenModifiers));
			else if (file.getName().endsWith(".class"))
				updateListIfSubclassing(list, rootClass, absoluteClassNameOf(file, rootClass.getPackage().getName()), requiredModifiers, forbiddenModifiers);
		}
		return list;
	}

	/**
	 * Returns a list of all (not abstract) classes which inherit from the given root class and which can be found from
	 * the given directory.
	 * 
	 * @param rootClass
	 *            a given class
	 * @param directory
	 *            a given directory
	 * @param requiredModifiers
	 *            a propagationSet of required modifiers for all subclasses
	 * @param forbiddenModifiers
	 *            a propagationSet of forbidden modifiers for all subclasses
	 */
	private static List<Class<?>> searchClassesInheretingFromInJar(Class<?> rootClass, String jarName, int requiredModifiers, int forbiddenModifiers) {
		List<Class<?>> list = new ArrayList<>();
		try (JarFile jf = new JarFile(jarName)) {
			Enumeration<JarEntry> enumeration = jf.entries();
			if (enumeration == null)
				return list;
			while (enumeration.hasMoreElements()) {
				String name = enumeration.nextElement().getName();
				String packTmp = replaceAll(rootClass.getPackage().getName(), '.', JAR_SEPARATOR_CHAR);
				if (!name.endsWith(".class") || !name.startsWith(packTmp))
					continue;
				// .class is removed and each '/' is replaced by '.' as in jar '/' is always the class separator
				name = replaceAll(name.substring(0, name.lastIndexOf(".")), JAR_SEPARATOR_CHAR, '.');
				updateListIfSubclassing(list, rootClass, name, requiredModifiers, forbiddenModifiers);
			}
		} catch (IOException e) {
			return null;
		}
		return list;
	}

	/**
	 * Returns the File object corresponding to the given directory.
	 * 
	 * @param classPathToken
	 *            a given path (element of the CLASSPATH environment variable)
	 * @param root
	 *            a given class
	 */
	private static File getDirectoryOf(String classPathToken, String basicDirectory) {
		return new File(classPathToken + (classPathToken.endsWith(File.separator) ? "" : File.separator) + replaceAll(basicDirectory, '.', File.separatorChar));
	}

	/**
	 * Returns all classes that inherit from the specified root class (by considering the CLASSPATH environment
	 * variable).
	 * 
	 * @param rootClass
	 *            a class
	 * @param requiredModifiers
	 *            a set of required modifiers for all subclasses
	 * @param forbiddenModifiers
	 *            a set of forbidden modifiers for all subclasses
	 * @return all classes that inherit from the specified root class
	 */
	private static Class<?>[] searchClassesInheritingFrom(Class<?> rootClass, int requiredModifiers, int forbiddenModifiers) {
		List<Class<?>> classes = new ArrayList<>();
		for (String token : System.getProperty("java.class.path", ".").split(File.pathSeparator)) {
			if (token.endsWith(".jar"))
				classes.addAll(searchClassesInheretingFromInJar(rootClass, token, requiredModifiers, forbiddenModifiers));
			else {
				File file = getDirectoryOf(token, rootClass.getPackage().getName());
				if (file.exists() && file.isDirectory())
					classes.addAll(searchClassesInheritingFromIn(rootClass, file, requiredModifiers, forbiddenModifiers));
			}
		}
		return classes.toArray(new Class[classes.size()]);
	}

	/**
	 * Returns all classes that inherit from the specified root class (by considering the CLASSPATH environment
	 * variable).
	 * 
	 * @param rootClass
	 *            a class
	 * @return all classes that inherit from the specified root class
	 */
	public static Class<?>[] searchClassesInheritingFrom(Class<?> rootClass) {
		return searchClassesInheritingFrom(rootClass, Modifier.PUBLIC, Modifier.ABSTRACT);
	}

	private static String searchClassInDirectory(File dir, String name) {
		for (File f : dir.listFiles())
			if (f.isDirectory()) {
				String path = searchClassInDirectory(f, name);
				if (path != null)
					return path;
			} else if (f.getName().equals(name))
				return f.getPath();
		return null;
	}

	private static String searchClassInJar(String jarName, String basicDirectory, String className) {
		try (JarFile jf = new JarFile(jarName)) {
			Enumeration<JarEntry> enumeration = jf.entries();
			if (enumeration == null)
				return null;
			while (enumeration.hasMoreElements()) {
				String name = enumeration.nextElement().getName();
				if (!name.startsWith(basicDirectory))
					continue;
				if (!name.substring(name.lastIndexOf('/') + 1).equals(className))
					continue;
				return replaceAll(name.substring(0, name.lastIndexOf(".")), JAR_SEPARATOR_CHAR, '.');
			}
		} catch (IOException e) {
			return null;
		}
		return null;
	}

	/**
	 * Returns the absolute name of the class whose name is specified.
	 * 
	 * @param basicPackage
	 *            the (absolute) name of a package
	 * @param className
	 *            the name of a class that must be found in the package (or sub-packages) whose name is specified
	 */
	private static String searchAbsoluteNameOf(String basicPackage, String className) {
		for (String classPathToken : System.getProperty("java.class.path", ".").split(File.pathSeparator)) {
			if (classPathToken.endsWith(".jar")) {
				String basicDirectory = replaceAll(basicPackage, '.', JAR_SEPARATOR_CHAR);
				// note that in jar '/' is always the class separator
				String path = searchClassInJar(classPathToken, basicDirectory, className + ".class");
				if (path != null)
					return path;
			} else {
				File f = getDirectoryOf(classPathToken, basicPackage);
				if (f.exists() && f.isDirectory()) {
					String path = searchClassInDirectory(f, className + ".class");
					if (path != null) {
						path = path.substring(classPathToken.length() + (classPathToken.endsWith(File.separator) ? 0 : 1), path.lastIndexOf("."));
						return replaceAll(path, File.separatorChar, '.');
					}
				}
			}
		}
		return null;
	}

	private static String computeAbsoluteClassName(String className, Class<?> rootClass) {
		String classPackageName = rootClass.getPackage().getName();
		int i = rootClass.getName().lastIndexOf('$');
		if (i != -1)
			className = rootClass.getName().substring(classPackageName.length() + 1, i + 1) + className;
		String key = classPackageName + className;
		String name = null;
		synchronized (mapOfClassNames) {
			name = mapOfClassNames.get(key);
			if (name == null) {
				name = searchAbsoluteNameOf(classPackageName, className);
				if (name == null)
					name = className; // at this point, it means that the class has been defined outside directory ace
				mapOfClassNames.put(key, name);
			}
		}
		return name;
	}

	/**
	 * Builds and returns an object of the class whose name is specified. The class must inherit from the specified root
	 * class. The constructor that is compatible with the specified parameters is called to build the object.
	 * 
	 * @param className
	 *            the name of a class
	 * @param rootClass
	 *            the root class of the object to be built
	 * @param parameters
	 *            the parameters to be used when building the object
	 * @return an object of the class whose name is given
	 */
	public static <T> T buildObject(String className, Class<T> rootClass, Object... parameters) {
		try {
			Class<?> cn = Class.forName(computeAbsoluteClassName(className, rootClass)), rcn = Class.forName(rootClass.getName());
			control(rcn.isAssignableFrom(cn), () -> className + " does not extend " + rootClass.getName());
			control(!Modifier.isAbstract(cn.getModifiers()), () -> className + " is abstract");
			for (Constructor<?> constructor : cn.getConstructors())
				if (constructor.getGenericParameterTypes().length == parameters.length)
					return (T) constructor.newInstance(parameters);
			return null;
		} catch (Exception e) {
			(e.getCause() == null ? e : e.getCause()).printStackTrace();
			return null;
		}
	}

	/**
	 * Builds and returns an object of the class whose name is specified. Be careful: the default constructor is used.
	 * 
	 * @param className
	 *            the name of a class
	 * @return an object of the class whose name is specified
	 */
	public static Object buildObject(String className) throws Exception {
		Constructor<?> c = Class.forName(className).getDeclaredConstructors()[0];
		c.setAccessible(true);
		return c.newInstance();
	}

	/**
	 * Builds and returns an object of the class whose name is specified. The class must be among those that are
	 * specified (inheriting from the type T). The constructor that is compatible with the specified parameters is
	 * called to build the object.
	 * 
	 * @param <T>
	 *            the root class of the object
	 * @param className
	 *            the name of a class
	 * @param classes
	 *            the set of possible target classes
	 * @param parameters
	 *            the parameters to be used when building the object
	 * @return an object of the class whose name is specified
	 */
	public static <T> T buildObject(String className, Set<Class<?>> classes, Object... parameters) {
		try {
			Class<?> clazz = null;
			if (className.indexOf('$') != -1 || className.indexOf('.') != -1)
				clazz = classes.stream().filter(c -> c.getName().endsWith(className)).findFirst().orElse(null);
			else
				clazz = classes.stream().filter(c -> c.getName().endsWith("$" + className) || c.getName().endsWith("." + className)).findFirst().orElse(null);
			control(clazz != null, () -> "It was impossible to load " + className);
			Constructor<?> cstr = Stream.of(clazz.getConstructors()).filter(c -> c.getGenericParameterTypes().length == parameters.length).findFirst()
					.orElse(null);
			control(cstr != null, () -> "It was impossible to find the appropriate constructor for " + className);
			return (T) cstr.newInstance(parameters);
		} catch (Exception e) {
			(e.getCause() == null ? e : e.getCause()).printStackTrace();
			return null;
		}
	}

}
