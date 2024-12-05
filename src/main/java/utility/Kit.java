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

import static java.util.stream.Collectors.joining;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Array;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Comparator;
import java.util.GregorianCalendar;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogManager;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.logging.StreamHandler;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.validation.SchemaFactory;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.Utilities;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import dashboard.Control;
import dashboard.Input;
import main.Head;

/**
 * This class contains many useful methods.
 * 
 * @author Christophe Lecoutre
 */
public final class Kit {

	/**
	 * The logger for ACE
	 */
	public static Logger log = Logger.getLogger("Logger ACE");

	/**
	 * The piece of code for initializing the logger
	 */
	static {
		LogManager.getLogManager().reset();
		Handler handler = new StreamHandler() {
			@Override
			public synchronized void publish(LogRecord record) {
				Control control = Thread.currentThread() instanceof Head ? ((Head) Thread.currentThread()).control : null;
				if (control != null && Input.portfolio)
					System.out.println("From " + control.userSettings.controlFilename + " :");
				if (record.getLevel().intValue() < Level.INFO.intValue())
					System.out.println(record.getMessage());
				else {
					// c.setTimeInMillis(record.getMillis());
					if (control != null && control.general.verbose > 1)
						System.err.println("\n" + record.getLevel() + " : " + record.getMessage());
					if (record.getLevel() == Level.SEVERE) {
						System.err.println(record.getLevel() + " forces us to stop");
						System.out.println("\ns UNSUPPORTED");
						System.exit(2);
					}
				}
			}
		};
		log.addHandler(handler);
	}

	/**
	 * Quits the program by displaying the specified message and exception
	 * 
	 * @param message
	 *            a message to be displayed
	 * @param e
	 *            an exception to be displayed
	 */
	public static Object exit(String message, Throwable e) {
		Color.RED.println("\n! ERROR: " + message + "\n  Use the solver option -ev for more details\n");
		if (!(Thread.currentThread() instanceof Head) || ((Head) Thread.currentThread()).control.general.exceptionsVisible)
			e.printStackTrace();
		Runtime.getRuntime().halt(0); // System.exit(1);
		// log.severe(message);
		return null;
	}

	/**
	 * Quits the program by displaying the specified message
	 * 
	 * @param message
	 *            a message to be displayed
	 */
	public static Object exit(String message) {
		return exit(message, new Exception());
	}

	/**
	 * Quits the program by displaying the specified exception
	 * 
	 * @param e
	 *            an exception to be displayed
	 */
	public static Object exit(Throwable e) {
		return exit("", e);
	}

	/**
	 * Controls that the specified condition is respected. Otherwise exits with the specified message
	 * 
	 * @param condition
	 *            a condition
	 * @param message
	 *            a message supplier to be displayed
	 */
	public static void control(boolean condition, Supplier<String> message) {
		if (!condition)
			exit(message.get(), new Exception());
	}

	/**
	 * Controls that the specified condition is respected. Otherwise exits with the specified message
	 * 
	 * @param condition
	 *            a condition
	 * @param message
	 *            a message to be displayed
	 */
	public static void control(boolean condition, String message) {
		if (!condition)
			exit(message, new Exception());
	}

	/**
	 * Controls that the specified condition is respected. Otherwise exits.
	 * 
	 * @param condition
	 *            a condition
	 */
	public static void control(boolean condition) {
		control(condition, "");
	}

	/**
	 * Copies a file to a target file
	 * 
	 * @param sourceFilename
	 *            the filename of the file to copy
	 * @param targetFilename
	 *            the filename of target file
	 */
	public static void copy(String sourceFilename, String targetFilename) {
		try {
			Files.copy(new File(sourceFilename).toPath(), new File(targetFilename).toPath(), StandardCopyOption.REPLACE_EXISTING);
		} catch (IOException e) {
			Kit.exit(e);
		}
	}

	public static <K, V extends Comparable<? super V>> Map<K, V> sort(Map<K, V> map, Comparator<? super Entry<K, V>> cmp) {
		Map<K, V> result = new LinkedHashMap<>();
		map.entrySet().stream().sorted(cmp).forEachOrdered(e -> result.put(e.getKey(), e.getValue()));
		return result;
	}

	/**********************************************************************************************
	 * Functions on Arrays
	 *********************************************************************************************/

	/**
	 * Builds and returns an array of the specified length with the specified value repeated
	 * 
	 * @param value
	 *            a value to be repeated
	 * @param length
	 *            the length of the array to be built
	 */
	public static int[] repeat(int value, int length) {
		int[] t = new int[length];
		Arrays.fill(t, value);
		return t;
	}

	/**
	 * Randomly reorders the specified array with the specified Random object. Implementing Fisher–Yates shuffle <br/>
	 * See https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
	 * 
	 * @param dense
	 *            an array to be shuffled
	 * @param random
	 *            a random object
	 */
	public static void shuffle(int[] dense, Random random) {
		for (int i = dense.length - 1; i > 0; i--) {
			int j = random.nextInt(i + 1);
			int tmp = dense[i];
			dense[i] = dense[j];
			dense[j] = tmp;
		}
	}

	/**
	 * @param start
	 *            the first value of the series that increases arithmetically by 1
	 * @param length
	 *            the length of the series
	 * @return an array of integers of the specified length with values: start, start + 1, start + 2 , ...
	 */
	public static int[] series(int start, int length) {
		Kit.control(length > 0);
		return IntStream.range(start, start + length).toArray();
	}

	/**
	 * @param length
	 *            the length of the series
	 * @return an array of integers of the specified length with values, 0, 1, 2 , ...
	 */
	public static int[] series(int length) {
		return series(0, length);
	}

	/**
	 * @param collection
	 *            a collection of short integers
	 * @return an array containing all short values from the specified collection
	 */
	public static short[] shortArray(Collection<Short> collection) {
		short[] t = new short[collection.size()];
		Iterator<Short> it = collection.iterator();
		for (int i = 0; i < t.length; i++)
			t[i] = it.next();
		return t;
	}

	/**
	 * @param array
	 *            an array of collections of short integers
	 * @return a matrix containing all short values from the specified array
	 */
	public static short[][] shortArray2D(Collection<Short>[] array) {
		return Stream.of(array).map(c -> shortArray(c)).toArray(short[][]::new);
	}

	/**
	 * @param collection
	 *            a collection of integers
	 * @return an array containing all values from the specified collection
	 */
	public static int[] intArray(Collection<Integer> collection) {
		return collection.stream().mapToInt(i -> i).toArray();
	}

	/**
	 * @param array
	 *            an array of collections of integers
	 * @return a matrix containing all values from the specified array
	 */
	public static int[][] intArray2D(Collection<Integer>[] array) {
		return Stream.of(array).map(c -> intArray(c)).toArray(int[][]::new);
	}

	/**
	 * @param value
	 *            an integer
	 * @param t
	 *            an array of integers
	 * @return true if the specified value is present in the specified array
	 */
	public static boolean isPresent(int value, int[] t) {
		for (int v : t)
			if (v == value)
				return true;
		return false;
	}

	/**
	 * @param t
	 *            an array of integers
	 * @return true if all values in the specified array are strictly increasingly ordered
	 */
	public static boolean isStrictlyIncreasing(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] >= t[i + 1]);
	}

	/**
	 * @param t
	 *            a matrix of integers
	 * @return true if all rows in the specified matrix are strictly increasingly ordered
	 */
	public static boolean isLexIncreasing(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> Utilities.lexComparatorInt.compare(t[i], t[i + 1]) >= 0);
	}

	/**
	 * @param value
	 *            a boolean
	 * @param t
	 *            an array of boolean
	 * @return the number of occurrences of the specified value in the specified array
	 */
	public static int countIn(boolean value, boolean[] t) {
		int cnt = 0;
		for (boolean b : t)
			if (b == value)
				cnt++;
		return cnt;
	}

	/**
	 * @param value
	 *            an integer
	 * @param t
	 *            an array of integers
	 * @return the number of occurrences of the specified value in the specified array
	 */
	public static int countIn(int value, int[] t) {
		int cnt = 0;
		for (int v : t)
			if (v == value)
				cnt++;
		return cnt;
	}

	/**
	 * Copies all values from the second specified array into the first specified array
	 * 
	 * @param src
	 *            a first array of integers
	 * @param dst
	 *            a second array of integers
	 */
	public static void copy(int[] src, int[] dst) {
		for (int i = dst.length - 1; i >= 0; i--)
			dst[i] = src[i];
	}

	/**
	 * Swaps the two integers in the specified array at the two specified indexes
	 * 
	 * @param tuple
	 * @param i
	 *            a first index
	 * @param j
	 *            a second index
	 * @return the same tuple
	 */
	public static int[] swap(int[] tuple, int i, int j) {
		int tmp = tuple[i];
		tuple[i] = tuple[j];
		tuple[j] = tmp;
		return tuple;
	}

	/**
	 * Swaps the two objects in the specified array at the two specified indexes
	 * 
	 * @param <T>
	 *            the type of the objects
	 * @param objects
	 *            an array of objects
	 * @param i
	 *            a first index
	 * @param j
	 *            a second index
	 */
	public static <T> void swap(T[] objects, int i, int j) {
		T tmp = objects[i];
		objects[i] = objects[j];
		objects[j] = tmp;
	}

	/**
	 * Swaps the two objects in the specified array
	 * 
	 * @param <T>
	 *            the type of the objects
	 * @param objects
	 *            an array of (two) objects
	 */
	public static <T> void swap(T[] objects) {
		control(objects.length == 2);
		swap(objects, 0, 1);
	}

	/**
	 * @param left
	 *            the first operand to be added
	 * @param right
	 *            the second operand to be added
	 * @return the sum of the two specified long, or exits in case of an overflow
	 */
	public static final long addSafe(long left, long right) {
		if (right > 0 ? left > Long.MAX_VALUE - right : left < Long.MIN_VALUE - right)
			Kit.exit("pb overflow " + left + " " + right);
		return left + right;
	}

	/**
	 * @param l
	 *            a long integer
	 * @return the value l possibly rounded to the extreme possible values of type Integer
	 */
	public static int round(long l) {
		return l <= Integer.MIN_VALUE ? Integer.MIN_VALUE : l >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) l;
	}

	private static void generatePermutations(List<int[]> perms, int[] t, int left, int right) {
		if (left == right)
			perms.add(t.clone());
		else
			for (int i = left; i <= right; i++) {
				swap(t, left, i);
				generatePermutations(perms, t, left + 1, right);
				swap(t, left, i);
			}
	}

	public static int[][] allPermutations(int[] values) {
		control(IntStream.range(0, values.length - 1).allMatch(i -> values[i] < values[i + 1]));
		control(2 <= values.length && values.length <= 10, "Current limit wrt our current needs");
		List<int[]> perms = new ArrayList<>();
		generatePermutations(perms, values, 0, values.length - 1);
		return perms.stream().toArray(int[][]::new);
	}

	/**********************************************************************************************
	 * Functions on Strings
	 *********************************************************************************************/

	/**
	 * Indicates if one really must use colors when the method 'coloring' is called
	 */
	public static boolean useColors = true;

	/**
	 * Different colors to be used when printing, for example, on the standard output
	 */
	public static enum Color {
		BLACK("\033[0;30m"),
		YELLOW("\u001b[33m"),
		CYAN("\033[0;36m"),
		PURPLE("\033[95m"),
		BLUE("\033[94m"),
		ORANGE("\033[93m"),
		RED("\033[91m"),
		GREEN("\033[92m"),
		WHITE_BOLD("\033[1m"),
		WHITE("\033[0m");

		private String code;

		private Color(String code) {
			this.code = code;
		}

		/**
		 * @param s
		 *            a string
		 * @return the specified string with this color (if colors can be used) or the same specified string
		 */
		public String coloring(String s) {
			return useColors ? this.code + s + WHITE.code : s;
		}

		/**
		 * Prints the specified first string with this color, if colors can be used (otherwise, in classical white color), followed by the specified second
		 * string in white
		 * 
		 * @param coloredPart
		 *            a string to be printed in color
		 * @param uncoloredPart
		 *            a string to be displayed in classical white color
		 */
		public void println(String coloredPart, String uncoloredPart) {
			System.out.println(coloring(coloredPart) + uncoloredPart);
		}

		/**
		 * Prints the specified string with this color, if colors can be used (otherwise, in classical white color)
		 * 
		 * @param s
		 *            a string to be printed
		 */
		public void println(String s) {
			System.out.println(coloring(s));
		}
	}

	/**
	 * Displays a warning based on the specified message
	 * 
	 * @param message
	 *            the message to display
	 */
	public static void warning(String message) {
		Color.ORANGE.println("\n  WARNING: " + message);
	}

	/**
	 * Returns the base name of the specified XML filename, i.e., the name without any path and any extension '.xml'
	 * 
	 * @param s
	 *            a string
	 * @return the base name of the specified XML filename
	 */
	public static String getXMLBaseNameOf(String s) {
		int first = s.lastIndexOf(File.separator);
		first = (first == -1 ? 0 : first + 1);
		int last = s.toLowerCase().lastIndexOf(".xml");
		last = (last == -1 ? s.length() : last);
		return s.substring(first, last);
	}

	/**
	 * @param pathAndFileName
	 *            a string
	 * @return the path of the specified filename
	 */
	public static String getPathOf(String pathAndFileName) {
		int last = pathAndFileName.lastIndexOf(File.separator);
		return last == -1 ? "" : pathAndFileName.substring(0, last + 1);
	}

	private static int maxDepthOf(Object o) {
		return o == null || !o.getClass().isArray() ? 0 : 1 + IntStream.range(0, Array.getLength(o)).map(i -> maxDepthOf(Array.get(o, i))).max().orElse(0);
	}

	private static String delimiterFor(int distToMaxDepth) {
		return distToMaxDepth == 0 ? " " : distToMaxDepth == 1 ? "\n" : distToMaxDepth == 2 ? "\n\n" : distToMaxDepth == 3 ? "\n\n\n" : "\n\n\n\n";
	}

	private static <T> StringBuilder join(StringBuilder sb, Object array, int length, int depth, int maxDepth, Function<T, String> mapper,
			String... delimiters) {
		for (int i = 0; i < length; i++) {
			Object item = Array.get(array, i);
			if (item == null)
				sb.append("null");
			else if (item.getClass().isArray())
				join(sb, item, Array.getLength(item), depth + 1, maxDepth, mapper, delimiters);
			else
				sb.append(mapper == null ? item.toString() : mapper.apply((T) item));
			sb.append(i < length - 1 ? (depth - 1 < delimiters.length ? delimiters[depth - 1] : delimiterFor(maxDepth - depth)) : "");
		}
		return sb;
	}

	private static <T> String join(Object array, int length, Function<T, String> mapper, String... delimiters) {
		return join(new StringBuilder(), array, length, 1, maxDepthOf(array), mapper, delimiters).toString();
	}

	/**
	 * @param array
	 *            an array of objects
	 * @param length
	 * @param delimiters
	 *            delimiters to be used when concatenating
	 * @return a string obtained by concatenating the string representation of the objects in the specified array, up to a limit given by the specified length,
	 *         while using the specified delimiters
	 */
	public static String join(Object array, int length, String... delimiters) {
		return join(new StringBuilder(), array, length, 1, maxDepthOf(array), null, delimiters).toString();
	}

	/**
	 * @param <T>
	 *            the type of objects subject to the mapper
	 * @param array
	 *            an array of objects
	 * @param mapper
	 *            a mapper to transform objects of the specified type
	 * @param delimiters
	 *            delimiters to be used when concatenating
	 * @return a string obtained by concatenating the string representation of the objects in the specified array while using the specified mapper for objects
	 *         of type T, and the specified delimiters
	 */
	public static <T> String join(Object array, Function<T, String> mapper, String... delimiters) {
		return join(array, Array.getLength(array), mapper, delimiters);
	}

	/**
	 * @param array
	 *            an array of objects
	 * @param delimiters
	 *            delimiters to be used when concatenating
	 * @return a string obtained by concatenating the string representation of the objects in the specified array while using the specified delimiters
	 */
	public static String join(Object array, String... delimiters) {
		return array == null ? "" : join(array, Array.getLength(array), delimiters);
	}

	/**
	 * @param c
	 *            a collection of objects
	 * @param delimiters
	 *            delimiters to be used when concatenating
	 * @return a string obtained by concatenating the string representation of the objects in the specified collection while using the specified delimiters
	 */
	public static String join(Collection<?> c, String... delimiters) {
		return join(c.toArray(), delimiters);
	}

	/**
	 * @return a string with the current date involving the year, month, day, hour, and minute
	 */
	public static String date() {
		Calendar c = new GregorianCalendar();
		c.setTimeInMillis(System.currentTimeMillis());
		return IntStream.of(Calendar.YEAR, Calendar.MONTH, Calendar.DAY_OF_MONTH, Calendar.HOUR_OF_DAY, Calendar.MINUTE).mapToObj(v -> "" + c.get(v))
				.collect(joining("_"));
	}

	/**
	 * @param clazz
	 *            a class
	 * @return a string with the last modified date of the file of the specified class, involving the year, month, day, hour, and minute
	 */
	public static String dateOf(Class<?> clazz) {
		try {
			File f = new File(clazz.getResource(clazz.getSimpleName() + ".class").toURI());
			return new SimpleDateFormat("(dd MMM yyyy 'at' HH:mm)").format(f.lastModified());
		} catch (Exception e) {
			return "";
		}
	}

	/**
	 * @return the amount of memory (in bytes) that is currently used by the JVM
	 */
	public static long memory() {
		Runtime rt = Runtime.getRuntime();
		return rt.totalMemory() - rt.freeMemory();
	}

	/**
	 * @return a string indicating in mega-bytes the amount of memory that is currently used by the JVM
	 */
	public static String memoryInMb() {
		long size = memory();
		long m = size / 1000000, k = size / 1000 - m * 1000;
		return m + "M" + k;
	}

	/**
	 * Analyzes the specified string in order to extract the id or number of objects (e.g., variables). This method is used to treat options set by the user
	 * concerning objects (possible priority variables or partial instantiations).
	 * 
	 * @param s
	 *            a string denoting a list of object ids and/or numbers
	 * @return an array with the ids or numbers of objects involved in the specified string
	 */
	public static Object[] extractFrom(String s) {
		if (s == null || s.trim().length() == 0)
			return new Object[0];
		Set<Object> set = new LinkedHashSet<>();
		for (String token : s.split(",")) {
			if (token.contains("..")) {
				control(token.matches("-?\\d+\\.\\.\\d+"), () -> " Pb with " + token);
				int[] t = Utilities.toIntegers(token.split("\\.\\."));
				for (int num = Math.abs(t[0]); num <= t[1]; num++)
					if (t[0] >= 0)
						set.add(num);
					else
						set.remove(num);
			} else {
				Integer num = Utilities.toInteger(token);
				if (num != null) {
					if (num >= 0)
						set.add(num);
					else
						set.remove(-num);
				} else
					set.add(token); // must be the id of an object (e.g., variable)
			}
		}
		return set.stream().toArray();
	}

	/*************************************************************************
	 ***** Inner classes
	 *************************************************************************/

	public static class ByteArrayHashKey {
		public byte[] t;

		public ByteArrayHashKey() {
		}

		public ByteArrayHashKey(byte[] t) {
			this.t = t;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(t);
		}

		@Override
		public boolean equals(Object obj) {
			return obj != null && getClass() == obj.getClass() && Arrays.equals(t, ((ByteArrayHashKey) obj).t);
		}
	}

	public static class IntArrayHashKey {
		public int[] t;

		public IntArrayHashKey() {
		}

		public IntArrayHashKey(int[] t) {
			this.t = t;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(t);
		}

		@Override
		public boolean equals(Object obj) {
			return obj != null && getClass() == obj.getClass() && Arrays.equals(t, ((IntArrayHashKey) obj).t);
		}
	}

	public static class LongArrayHashKey {
		public long[] t;

		public LongArrayHashKey() {
		}

		public LongArrayHashKey(long[] t) {
			this.t = t;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(t);
		}

		@Override
		public boolean equals(Object obj) {
			return obj != null && getClass() == obj.getClass() && Arrays.equals(t, ((LongArrayHashKey) obj).t);
		}
	}

	/*************************************************************************
	 ***** Handling Documents
	 *************************************************************************/

	private static Object handleException(Exception e) {
		if (e instanceof SAXException) { // superclass of SAXParseException
			Kit.log.warning("\n** SAX error " + ((SAXParseException) e).getMessage());
			if (e instanceof SAXParseException)
				Kit.log.warning("  at line " + ((SAXParseException) e).getLineNumber() + ", uri " + ((SAXParseException) e).getSystemId());
			(((SAXException) e).getException() == null ? e : ((SAXException) e).getException()).printStackTrace();
		} else if (e instanceof TransformerException) {
			Kit.log.warning("\n** Transformation error" + e.getMessage());
			(((TransformerException) e).getException() == null ? e : ((TransformerException) e).getException()).printStackTrace();
		}
		return Kit.exit(e);
	}

	/**
	 * Creates and returns a new (empty) XML document
	 * 
	 * @return a document
	 */
	public static Document createNewDocument() {
		try {
			return DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
		} catch (ParserConfigurationException e) {
			return (Document) handleException(e);
		}
	}

	/**
	 * Builds a Document (DOM object) corresponding to the specified input stream.
	 * 
	 * @param inputStream
	 *            the input stream that denotes the XML document to be loaded.
	 * @param schema
	 *            the schema to be used (<code> null </code> if not used) to validate the document
	 * @return a document
	 */
	private static Document load(InputStream inputStream, URL schema) {
		try {
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_DTD, ""); // Compliant
			factory.setAttribute(XMLConstants.ACCESS_EXTERNAL_SCHEMA, ""); // compliant
			factory.setNamespaceAware(true);
			if (schema != null)
				factory.setSchema(SchemaFactory.newInstance("http://www.w3.org/2001/XMLSchema").newSchema(schema));
			return factory.newDocumentBuilder().parse(inputStream);
		} catch (Exception e) {
			return (Document) handleException(e);
		}
	}

	/**
	 * Loads the specified XML file
	 * 
	 * @param file
	 *            a file
	 * @return a document
	 */
	public static Document load(File file) {
		try (FileInputStream f = new FileInputStream(file)) {
			return load(f, null); // no schema
		} catch (FileNotFoundException e) {
			return (Document) Kit.exit("File " + file.getName() + " does not exist", e);
		} catch (IOException e1) {
			e1.printStackTrace();
			return null;
		}
	}

	/**
	 * Loads the XML file whose name is specified
	 * 
	 * @param fileName
	 *            a filename
	 * @return a document
	 */
	public static Document load(String fileName) {
		if (fileName.endsWith("xml.bz2") || fileName.endsWith("xml.lzma"))
			try {
				Process p = Runtime.getRuntime().exec((fileName.endsWith("xml.bz2") ? "bunzip2 -c " : "lzma -c -d ") + fileName);
				try (InputStream is = p.getInputStream()) {
					Document document = load(is, null);
					p.waitFor();
					p.exitValue();
					p.destroy();
					return document;
				} catch (Exception e) {
					return (Document) Kit.exit("Problem with " + fileName, e);
				}
			} catch (Exception e) {
				return (Document) Kit.exit("Problem with " + fileName, e);
			}
		return load(new File(fileName));
	}

	/**
	 * Modifies the specified document by setting the specified attribute value to the specified attribute name, when considering the specified path
	 * 
	 * @param document
	 *            a document
	 * @param path
	 *            a path in the document
	 * @param attName
	 *            the name of an attribute
	 * @param attValue
	 *            the (new) value of the attribute
	 */
	public static void modify(Document document, String path, String attName, String attValue) {
		try {
			NodeList result = (NodeList) XPathFactory.newInstance().newXPath().compile("//" + path).evaluate(document, XPathConstants.NODESET);
			Kit.control(result.getLength() == 1, () -> path + " " + result.getLength());
			((Element) result.item(0)).setAttribute(attName, attValue);
		} catch (Exception e) {
			Kit.exit("Pb with " + path, e);
		}
	}

	/**
	 * Returns the value of the specified attribute for the specified tag, in the document whose filename is specified
	 * 
	 * @param fileName
	 *            the name of an XML file
	 * @param tagName
	 *            the name of a tag
	 * @param attName
	 *            the name of an attribute
	 * @return the value of the specified attribute for the specified tag, in the document whose filename is specified
	 */
	public static String attValueFor(String fileName, String tagName, String attName) {
		return ((Element) load(fileName).getElementsByTagName(tagName).item(0)).getAttribute(attName);
	}

	/**
	 * Returns true if the root of the specified XML file has a name starting with the specified string
	 * 
	 * @param fileName
	 *            the name of an XML file
	 * @param rootToken
	 *            a string
	 * @return true if the root of the specified XML file has a name starting with the specified string
	 */
	public static boolean isXMLFileWithRoot(String fileName, String rootToken) {
		File file = new File(fileName);
		if (!file.isFile())
			return false;
		try (BufferedReader in = new BufferedReader(new FileReader(file))) {
			String line = in.readLine();
			while (line != null && (line.trim().isEmpty() || line.startsWith("<?xml")))
				line = in.readLine();
			return line != null && line.trim().startsWith("<" + rootToken);
		} catch (Exception e) {
			return (Boolean) Kit.exit("Problem with " + fileName, e);
		}
	}

	/**
	 * Returns the greatest integer x such that c*x <= k where c and k are specified integers. <br />
	 * The coefficient must be positive, as we note that (3,-5) => -2; (3,10) => 3; (-3,-5) => 2; (-3,10) => -3; (3,0) => 0; (-3,0) => 0 <br/>
	 * 3y <= -5 => y <= -2; 3y <= 10 => y <= 3; -3y <= -5 => y >= 2; -3y <= 10 => y >= -3; 3y <= 0 => y <= 0; -3y <= 0 => y >= 0
	 * 
	 * @param c
	 *            a coefficient
	 * @param k
	 *            a limit
	 * @return the greatest integer x such that c*x <= k
	 */
	public static int greatestIntegerLE(int c, int k) { // c*x <= k
		control(c >= 0);
		if (c == 0)
			return k >= 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE;
		int limit = k / c;
		double ll = k / (double) c;
		if (k < 0 && k % c != 0)
			limit += (ll < 0 ? -1 : 1);
		return limit;
	}

	/**
	 * Returns the smallest integer x such that c*x >= k where c and k are specified integers. <br />
	 * The coefficient must be positive, as we note that (3,-5) => -1; (3,10) => 4; (-3,-5) => 1; (-3,10) => -4; (3,0) => 0; (-3,0) => 0 <br />
	 * 3y >= -5 => y >= -1; 3y >= 10 => y >= 4; -3y >= -5 => y <= 1; -3y >= 10 => y <= -4; 3y >= 0 => y>= 0; -3y >= 0 => y <= 0
	 * 
	 * @param c
	 *            a coefficient
	 * @param k
	 *            a limit
	 * @return the smallest integer x such that c*x >= k
	 */
	public static int smallestIntegerGE(int c, int k) { // c*x >= k
		control(c >= 0);
		if (c == 0)
			return k <= 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE;
		int limit = k / c;
		double ll = k / (double) c;
		if (k > 0 && k % c != 0)
			limit += (ll < 0 ? -1 : 1);
		return limit;
	}

	public static void main(String[] args) {
		System.out.println(-1 / 9.0 + "");
		for (int[] t : new int[][] { { 3, -5 }, { 3, 10 }, { -3, -5 }, { -3, 10 }, { 3, 0 }, { -3, 0 }, { 10, -20 }, { 9, -1 }, { -10, -1 } })
			System.out.println(t[0] + " " + t[1] + " => " + greatestIntegerLE(t[0], t[1]));
		System.out.println();
		for (int[] t : new int[][] { { 3, -5 }, { 3, 10 }, { -3, -5 }, { -3, 10 }, { 3, 0 }, { -3, 0 }, { -10, 20 }, { -3, 5 }, { -9, 1 }, { 10, 1 } })
			System.out.println(t[0] + " " + t[1] + " => " + smallestIntegerGE(t[0], t[1]));
	}

}