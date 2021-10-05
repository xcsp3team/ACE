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
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Comparator;
import java.util.GregorianCalendar;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogManager;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.logging.StreamHandler;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.validation.SchemaFactory;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.IVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNode;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import dashboard.Control;
import dashboard.Input;
import main.Head;

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
				if (record.getLevel().intValue() < Level.INFO.intValue()) {
					if (Input.portfolio)
						System.out.println("From " + control.userSettings.controlFilename + " :");
					System.out.println(record.getMessage());
				} else {
					if (Input.portfolio)
						System.err.println("From " + control.userSettings.controlFilename + " :");
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
		System.out.println(preprint("\n! ERROR with message: " + message + "\n  Use the solver option -ev for more details\n", RED));
		if (!(Thread.currentThread() instanceof Head) || ((Head) Thread.currentThread()).control.general.exceptionsVisible)
			e.printStackTrace();
		System.exit(1);
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

	public static int[] range(int minIncluded, int maxIncluded) {
		Kit.control(minIncluded <= maxIncluded);
		return IntStream.range(minIncluded, maxIncluded + 1).toArray();
	}

	public static int[] range(int length) {
		return range(0, length - 1);
	}

	public static int[][] cloneDeeply(int[][] m) {
		return Stream.of(m).map(t -> t.clone()).toArray(int[][]::new);
	}

	public static long[][] cloneDeeply(long[][] m) {
		return Stream.of(m).map(t -> t.clone()).toArray(long[][]::new);
	}

	public static void fill(boolean[][] m, boolean value) {
		for (boolean[] t : m)
			Arrays.fill(t, value);
	}

	public static short[] shortArray(Collection<Short> collection) {
		short[] t = new short[collection.size()];
		Iterator<Short> it = collection.iterator();
		for (int i = 0; i < t.length; i++)
			t[i] = it.next();
		return t;
	}

	public static short[][] shortArray2D(Collection<Short>[] array) {
		return Stream.of(array).map(c -> shortArray(c)).toArray(short[][]::new);
	}

	public static int[] intArray(Collection<Integer> collection) {
		return collection.stream().mapToInt(i -> i).toArray();
	}

	public static int[][] intArray2D(Collection<Integer>[] array) {
		return Stream.of(array).map(c -> intArray(c)).toArray(int[][]::new);
	}

	public static int[][] intArray2D(Collection<int[]> collection) {
		return collection.stream().toArray(int[][]::new);
	}

	public static boolean isPresent(int value, int[] t) {
		for (int v : t)
			if (v == value)
				return true;
		return false;
	}

	public static boolean isStrictlyIncreasing(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] >= t[i + 1]);
	}

	public static boolean isLexIncreasing(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> Utilities.lexComparatorInt.compare(t[i], t[i + 1]) > 0);
	}

	public static int countIn(boolean value, boolean[] t) {
		int cnt = 0;
		for (boolean b : t)
			if (b == value)
				cnt++;
		return cnt;
	}

	public static int countIn(int value, int[] t) {
		int cnt = 0;
		for (int v : t)
			if (v == value)
				cnt++;
		return cnt;
	}

	public static void copy(int[] src, int[] dst) {
		for (int i = dst.length - 1; i >= 0; i--)
			dst[i] = src[i];
	}

	public static int[] swap(int[] tuple, int i, int j) {
		int tmp = tuple[i];
		tuple[i] = tuple[j];
		tuple[j] = tmp;
		return tuple;
	}

	public static <T> void swap(T[] objects, int i, int j) {
		T tmp = objects[i];
		objects[i] = objects[j];
		objects[j] = tmp;
	}

	public static <T> void swap(T[] objects) {
		control(objects.length == 2);
		swap(objects, 0, 1);
	}

	public static final long addSafe(long left, long right) {
		if (right > 0 ? left > Long.MAX_VALUE - right : left < Long.MIN_VALUE - right)
			Kit.exit("pb overflow " + left + " " + right);
		return left + right;
	}

	public static int[] buildMapping(int[] src, int[] dst) {
		int[] mapping = new int[src.length];
		for (int i = 0; i < src.length; i++)
			mapping[i] = Utilities.indexOf(src[i], dst);
		return mapping;
	}

	public static <E> E[] sort(E[] t, Comparator<E> comparator) {
		Arrays.sort(t, comparator);
		return t;
	}

	public static Long parseLong(String token) {
		try {
			return Long.parseLong(token);
		} catch (NumberFormatException e) {
			return null;
		}
	}

	public static int trunc(long l) {
		return l <= Integer.MIN_VALUE ? Integer.MIN_VALUE : l >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) l;
	}

	/**********************************************************************************************
	 * Functions on Strings
	 *********************************************************************************************/

	public static boolean useColors = true;

	public static final String BLACK = "\033[0;30m";
	public static final String YELLOW = "\u001b[33m";
	public static final String CYAN = "\033[0;36m";
	public static final String PURPLE = "\033[95m";
	public static final String BLUE = "\033[94m";
	public static final String ORANGE = "\033[93m";
	public static final String RED = "\033[91m";
	public static final String GREEN = "\033[92m";
	public static final String WHITE_BOLD = "\033[1m";
	public static final String WHITE = "\033[0m";

	public static String preprint(String s, String color) {
		return useColors ? color + s + WHITE : s;
	}

	public static String getXMLBaseNameOf(String s) {
		int first = s.lastIndexOf(File.separator);
		first = (first == -1 ? 0 : first + 1);
		int last = s.toLowerCase().lastIndexOf(".xml");
		last = (last == -1 ? s.length() : last);
		return s.substring(first, last);
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

	public static String join(Object array, int length, String... delimiters) {
		return join(new StringBuilder(), array, length, 1, maxDepthOf(array), null, delimiters).toString();
	}

	public static <T> String join(Object array, Function<T, String> mapper, String... delimiters) {
		return join(array, Array.getLength(array), mapper, delimiters);
	}

	public static String join(Object array, String... delimiters) {
		return join(array, Array.getLength(array), delimiters);
	}

	public static String join(Collection<?> c, String... delimiters) {
		return join(c.toArray(), delimiters);
	}

	public static String getPathOf(String pathAndFileName) {
		int last = pathAndFileName.lastIndexOf("/");
		return last == -1 ? "" : pathAndFileName.substring(0, last + 1);
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
		public boolean equals(Object object) {
			return Arrays.equals(t, ((ByteArrayHashKey) object).t);
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
		public boolean equals(Object object) {
			return Arrays.equals(t, ((IntArrayHashKey) object).t);
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
		public boolean equals(Object object) {
			return Arrays.equals(t, ((LongArrayHashKey) object).t);
		}
	}

	public static String date() {
		Calendar c = new GregorianCalendar();
		c.setTimeInMillis(System.currentTimeMillis());
		return IntStream.of(Calendar.YEAR, Calendar.MONTH, Calendar.DAY_OF_MONTH, Calendar.HOUR_OF_DAY, Calendar.MINUTE).mapToObj(v -> "" + c.get(v))
				.collect(Collectors.joining("_"));
	}

	public static String dateOf(Class<?> clazz) {
		try {
			File f = new File(clazz.getResource(clazz.getSimpleName() + ".class").toURI());
			return new SimpleDateFormat("(dd MMM yyyy 'at' HH:mm)").format(f.lastModified()).toString();
		} catch (Exception e) {
			return "";
		}
	}

	public static long memory() {
		Runtime rt = Runtime.getRuntime();
		return rt.totalMemory() - rt.freeMemory();
	}

	public static String memoryInMb() {
		long size = memory();
		long m = size / 1000000, k = size / 1000 - m * 1000;
		return m + "M" + k;
	}

	/*************************************************************************
	 ***** Handling Documents
	 *************************************************************************/

	public static final String W3C_XML_SCHEMA = "http://www.w3.org/2001/XMLSchema";

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

	public static Document createNewDocument() {
		try {
			return DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
		} catch (ParserConfigurationException e) {
			return (Document) handleException(e);
		}
	}

	/**
	 * Build a DOM object that corresponds to the specified input stream.
	 * 
	 * @param inputStream
	 *            the input stream that denotes the XML document to be loaded.
	 * @param schema
	 *            the schema to be used (<code> null </code> if not used) to validate the document
	 * @return a DOM object
	 */
	private static Document load(InputStream is, URL schema) {
		try {
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			factory.setNamespaceAware(true);
			if (schema != null)
				factory.setSchema(SchemaFactory.newInstance(W3C_XML_SCHEMA).newSchema(schema));
			return factory.newDocumentBuilder().parse(is);
		} catch (Exception e) {
			return (Document) handleException(e);
		}
	}

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

	public static Document load(String fileName) {
		if (fileName.endsWith("xml.bz2") || fileName.endsWith("xml.lzma"))
			try {
				Process p = Runtime.getRuntime().exec((fileName.endsWith("xml.bz2") ? "bunzip2 -c " : "lzma -c -d ") + fileName);
				Document document = load(p.getInputStream(), null);
				p.waitFor();
				p.exitValue();
				p.destroy();
				return document;
			} catch (Exception e) {
				return (Document) Kit.exit("Problem with " + fileName, e);
			}
		return load(new File(fileName));
	}

	public static void modify(Document document, String path, String attName, String attValue) {
		try {
			NodeList result = (NodeList) XPathFactory.newInstance().newXPath().compile("//" + path).evaluate(document, XPathConstants.NODESET);
			Kit.control(result.getLength() == 1, () -> path + " " + result.getLength());
			((Element) result.item(0)).setAttribute(attName, attValue);
		} catch (Exception e) {
			Kit.exit("Pb with " + path, e);
		}
	}

	public static String attValueFor(String fileName, String tagName, String attName) {
		return ((Element) load(fileName).getElementsByTagName(tagName).item(0)).getAttribute(attName);
	}

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

	public static <T extends IVar> T[] vars(Object... objects) {
		return (T[]) Utilities.collect(IVar.class, Stream.of(objects).map(o -> o instanceof XNode ? ((XNode<?>) o).vars() : o));
	}

	// (3,-5) => -2; (3,10) => 3; (-3,-5) => 2; (-3,10) => -3; (3,0) => 0; (-3,0) => 0
	// 3y <= -5 => y <= -2; 3y <= 10 => y <= 3; -3y <= -5 => y >= 2; -3y <= 10 => y >= -3; 3y <= 0 => y <= 0; -3y <= 0
	// => y >= 0
	public static int greatestIntegerLE(int c, int k) { // c*y <= k
		if (c == 0)
			return k >= 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE;
		int limit = k / c;
		double ll = k / (double) c;
		if (k < 0 && k % c != 0)
			limit += (ll < 0 ? -1 : 1);
		return limit;
	}

	// (3,-5) => -1; (3,10) => 4; (-3,-5) => 1; (-3,10) => -4; (3,0) => 0; (-3,0) => 0
	// 3y >= -5 => y >= -1; 3y >= 10 => y >= 4; -3y >= -5 => y <= 1; -3y >= 10 => y <= -4; 3y >= 0 => y>= 0; -3y >= 0 =>
	// y <= 0
	public static int smallestIntegerGE(int c, int k) { // c*y >= k
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