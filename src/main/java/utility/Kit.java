/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.InputStream;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.net.URL;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Comparator;
import java.util.GregorianCalendar;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.StringTokenizer;
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
import java.util.stream.LongStream;
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

import dashboard.Input;
import main.Head;

public final class Kit {
	private Kit() {
	}

	public static DecimalFormat decimalFormat = new DecimalFormat("###.##", new DecimalFormatSymbols(Locale.ENGLISH));
	public static DecimalFormatSymbols symbols = new DecimalFormatSymbols(Locale.US);
	public static DecimalFormat df2 = new DecimalFormat("0.00", symbols);
	public static DecimalFormat df1 = new DecimalFormat("0.0", symbols);
	public static DecimalFormat df0 = new DecimalFormat("00");

	public static Logger log = Logger.getLogger("Logger ACE");
	static {
		LogManager.getLogManager().reset();
		Handler handler = new StreamHandler() {
			@Override
			public void publish(LogRecord record) {
				if (record.getLevel().intValue() < Level.INFO.intValue()) {
					if (Input.multiThreads)
						System.out.println("From " + ((Head) Thread.currentThread()).control.settingsFilename + " :");
					System.out.println(record.getMessage());
				} else {
					if (Input.multiThreads)
						System.err.println("From " + ((Head) Thread.currentThread()).control.settingsFilename + " :");
					// c.setTimeInMillis(record.getMillis());
					Thread t = Head.currentThread();
					if (t instanceof Head && ((Head) t).control.general.verbose > 1)
						System.err.println("\n" + record.getLevel() + " : " + record.getMessage()); // + " " + c.getTime());
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

	public static void copy(String srcFileName, String dstFileName) {
		try (BufferedInputStream in = new BufferedInputStream(new FileInputStream(srcFileName));
				BufferedOutputStream out = new BufferedOutputStream(new FileOutputStream(dstFileName));) {
			byte[] bytes = new byte[1024];
			for (int nb = in.read(bytes, 0, bytes.length); nb > 0; nb = in.read(bytes, 0, bytes.length))
				out.write(bytes, 0, nb);
		} catch (Exception e) {
			Kit.exit(e);
		}
	}

	public static Object control(boolean conditionToBeRespected, Supplier<String> message) {
		return conditionToBeRespected ? null : exit(message.get(), new Exception());
	}

	public static Object control(boolean conditionToBeRespected, String message) {
		return conditionToBeRespected ? null : exit(message, new Exception());
	}

	public static Object control(boolean conditionToBeRespected) {
		return control(conditionToBeRespected, () -> "");
	}

	public static Object exit(String message, Throwable e) {
		System.out.println(preprint("\n! ERROR with message: " + message + "\n  Use the solver option -ev for more details\n", RED));
		if (!(Thread.currentThread() instanceof Head) || ((Head) Thread.currentThread()).control.general.makeExceptionsVisible)
			e.printStackTrace();
		System.exit(1);
		// log.severe(message);
		return null;
	}

	public static Object exit(String message) {
		return exit(message, new Exception());
	}

	public static Object exit(Throwable e) {
		return exit("", e);
	}

	private static void collectObjects(Object o, List<Object> list) {
		if (o != null)
			if (o.getClass().isArray())
				IntStream.range(0, Array.getLength(o)).forEach(i -> collectObjects(Array.get(o, i), list));
			else
				list.add(o);
	}

	/**
	 * Builds a 1-dimensional array of objects from the specified sequence of parameters. Each element of the sequence must only contain variables (and possibly
	 * null values), either stand-alone or present in arrays (of any dimension). All variables are collected in order, and concatenated to form a 1-dimensional
	 * array. Note that null values are simply discarded.
	 */
	public static Object[] concat(Object first, Object... next) {
		List<Object> list = new ArrayList<>();
		collectObjects(first, list);
		Stream.of(next).forEach(o -> collectObjects(o, list));
		return list.toArray(new Object[list.size()]);
	}

	public static final Comparator<int[]> lexComparatorInt = (t1, t2) -> {
		for (int i = 0; i < t1.length; i++)
			if (t1[i] < t2[i])
				return -1;
			else if (t1[i] > t2[i])
				return +1;
		return 0;
	};

	public static final Comparator<long[]> lexComparatorLong = (t1, t2) -> {
		for (int i = 0; i < t1.length; i++)
			if (t1[i] < t2[i])
				return -1;
			else if (t1[i] > t2[i])
				return +1;
		return 0;
	};

	public static <K, V extends Comparable<? super V>> Map<K, V> sort(Map<K, V> map, Comparator<? super Entry<K, V>> cmp) {
		Map<K, V> result = new LinkedHashMap<>();
		map.entrySet().stream().sorted(cmp).forEachOrdered(e -> result.put(e.getKey(), e.getValue()));
		return result;
	}

	public static String capitalize(String s) {
		char[] t = s.toCharArray();
		IntStream.range(0, t.length).forEach(i -> t[i] = i == 0 ? Character.toUpperCase(t[i]) : Character.toLowerCase(t[i]));
		return new String(t);
	}

	public static String camelCaseOf(String s) {
		return Stream.of(s.split("_")).map(tok -> capitalize(tok)).collect(Collectors.joining());
	}

	public static boolean[] and(boolean[] inOut, boolean[] in) {
		assert inOut.length == in.length;
		for (int i = 0; i < inOut.length; i++)
			inOut[i] = inOut[i] && in[i];
		return inOut;
	}

	public static boolean[] or(boolean[] inOut, boolean[] in) {
		assert inOut.length == in.length;
		for (int i = 0; i < inOut.length; i++)
			inOut[i] = inOut[i] || in[i];
		return inOut;
	}

	public static boolean isSubsumed(boolean[] t1, boolean[] t2) {
		assert t1.length == t2.length;
		for (int i = 0; i < t1.length; i++)
			if (t1[i] && !t2[i])
				return false;
		return true;
	}

	public static boolean[] repeat(boolean value, int length) {
		boolean[] t = new boolean[length];
		Arrays.fill(t, value);
		return t;
	}

	public static char[] repeat(char value, int length) {
		char[] t = new char[length];
		Arrays.fill(t, value);
		return t;
	}

	public static short[] repeat(short value, int length) {
		short[] t = new short[length];
		Arrays.fill(t, value);
		return t;
	}

	public static int[] repeat(int value, int length) {
		int[] t = new int[length];
		Arrays.fill(t, value);
		return t;
	}

	public static long[] repeat(long value, int length) {
		long[] t = new long[length];
		Arrays.fill(t, value);
		return t;
	}

	public static double[] repeat(double value, int length) {
		double[] t = new double[length];
		Arrays.fill(t, value);
		return t;
	}

	public static int[][] repeat(int value, int length1, int length2) {
		int[][] m = new int[length1][length2];
		for (int[] t : m)
			Arrays.fill(t, value);
		return m;
	}

	// Implementing Fisher–Yates shuffle (see https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle)
	public static void shuffle(int[] dense, Random random) {
		for (int i = dense.length - 1; i > 0; i--) {
			int j = random.nextInt(i + 1);
			int tmp = dense[i];
			dense[i] = dense[j];
			dense[j] = tmp;
		}
	}

	public static byte[] range(byte length) {
		Kit.control(0 < length);
		byte[] t = new byte[length];
		for (byte i = 0; i < t.length; i++)
			t[i] = i;
		return t;
	}

	public static short[] range(short minIncluded, short maxIncluded) {
		Kit.control(minIncluded <= maxIncluded, () -> minIncluded + ".." + maxIncluded);
		short[] t = new short[maxIncluded - minIncluded + 1];
		for (short i = minIncluded; i <= maxIncluded; i++)
			t[i - minIncluded] = i;
		return t;
	}

	public static short[] range(short length) {
		return range((short) 0, (short) (length - 1));
	}

	public static int[] range(int minIncluded, int maxIncluded, int step) {
		Kit.control(minIncluded <= maxIncluded);
		List<Integer> list = new ArrayList<>();
		for (int i = minIncluded; i <= maxIncluded; i += step)
			list.add(i);
		return Kit.intArray(list);
	}

	public static int[] range(int minIncluded, int maxIncluded) {
		Kit.control(minIncluded <= maxIncluded);
		return IntStream.range(minIncluded, maxIncluded + 1).toArray();
	}

	public static int[] range(int length) {
		return range(0, length - 1);
	}

	public static long[] range(long length) {
		Kit.control(0 < length && length <= Integer.MAX_VALUE);
		return LongStream.range(0, length).toArray();
	}

	public static boolean[][] cloneDeeply(boolean[][] m) {
		return Stream.of(m).map(t -> t.clone()).toArray(boolean[][]::new);
	}

	public static boolean[][][] cloneDeeply(boolean[][][] c) {
		return Stream.of(c).map(m -> cloneDeeply(m)).toArray(boolean[][][]::new);
	}

	public static int[][] cloneDeeply(int[][] m) {
		return Stream.of(m).map(t -> t.clone()).toArray(int[][]::new);
	}

	public static int[][][] cloneDeeply(int[][][] c) {
		return Stream.of(c).map(m -> cloneDeeply(m)).toArray(int[][][]::new);
	}

	public static long[][] cloneDeeply(long[][] m) {
		return Stream.of(m).map(t -> t.clone()).toArray(long[][]::new);
	}

	public static void fill(boolean[][] m, boolean value) {
		for (boolean[] t : m)
			Arrays.fill(t, value);
	}

	public static void fill(int[][] m, int value) {
		for (int[] t : m)
			Arrays.fill(t, value);
	}

	public static void fill(Object[][] m, Object value) {
		for (Object[] t : m)
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

	public static short[][][] shortArray3D(Collection<Short>[][] array) {
		return Stream.of(array).map(c -> shortArray2D(c)).toArray(short[][][]::new);
	}

	public static int[][] intArray2D(Collection<Integer>[] array) {
		return Stream.of(array).map(c -> intArray(c)).toArray(int[][]::new);
	}

	public static int[][][] intArray3D(Collection<Integer>[][] array) {
		return Stream.of(array).map(c -> intArray2D(c)).toArray(int[][][]::new);
	}

	public static int[] intArray(Collection<Integer> collection) {
		return collection.stream().mapToInt(i -> i).toArray();
	}

	public static int[][] intArray2D(Collection<int[]> collection) {
		return collection.stream().toArray(int[][]::new);
	}

	public static int[][][] intArray3D(Collection<int[][]> collection) {
		return collection.stream().toArray(int[][][]::new);
	}

	/**********************************************************************************************
	 * Search in Arrays
	 *********************************************************************************************/

	/**
	 * Returns true iff the specified value belongs to the specified array. Comparison are made by references.
	 */
	public static <T> boolean isPresent(T value, T[] t) {
		for (T v : t)
			if (v == value)
				return true;
		return false;
	}

	public static <T> boolean isPresent(String s, String[][] m) {
		for (String[] t : m)
			if (isPresent(s, t))
				return true;
		return false;
	}

	public static boolean isPresent(int value, int[] t) {
		for (int v : t)
			if (v == value)
				return true;
		return false;
	}

	public static boolean isPresent(int value, int[]... m) {
		for (int[] t : m)
			if (isPresent(value, t))
				return true;
		return false;
	}

	public static boolean withNoNegativeValues(long[][] m) {
		return Stream.of(m).noneMatch(t -> Arrays.stream(t).anyMatch(v -> v < 0));
	}

	public static boolean allDifferentValues(int[] t, int... except) {
		for (int i = 0; i < t.length; i++) {
			if (Utilities.indexOf(t[i], except) != -1)
				continue;
			for (int j = i + 1; j < t.length; j++)
				if (t[i] == t[j])
					return false;
		}
		return true;
	}

	/**********************************************************************************************
	 * 
	 *********************************************************************************************/

	public static boolean isIncreasing(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] > t[i + 1]);
	}

	public static boolean isStrictlyIncreasing(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] >= t[i + 1]);
	}

	public static boolean isIncreasing(double[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] > t[i + 1]);
	}

	public static <T extends Comparable<T>> boolean isStrictlyIncreasing(T[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i].compareTo(t[i + 1]) >= 0);
	}

	public static boolean isLexIncreasing(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> Utilities.lexComparatorInt.compare(t[i], t[i + 1]) > 0);
	}

	public static int countIn(boolean value, boolean[] t) {
		return IntStream.range(0, t.length).filter(i -> t[i] == value).map(i -> 1).sum();
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

	public static int[] sort(int[] t) {
		Arrays.sort(t);
		return t;
	}

	public static long[] sort(long[] t) {
		Arrays.sort(t);
		return t;
	}

	public static double[] sort(double[] t) {
		Arrays.sort(t);
		return t;
	}

	public static <E> E[] sort(E[] t) {
		Arrays.sort(t);
		return t;
	}

	public static <E> E[] sort(E[] t, Comparator<E> comparator) {
		Arrays.sort(t, comparator);
		return t;
	}

	public static String getRawInstanceName(String s) {
		int first = s.lastIndexOf(File.separator) != -1 ? s.lastIndexOf(File.separator) + 1 : 0;
		int last = s.lastIndexOf(".") != -1 ? s.lastIndexOf(".") : s.length();
		return first > last ? s.substring(first) : s.substring(first, last);
	}

	public static String getXMLBaseNameOf(String s) {
		int first = s.lastIndexOf(File.separator);
		first = (first == -1 ? 0 : first + 1);
		int last = s.toLowerCase().lastIndexOf(".xml");
		last = (last == -1 ? s.length() : last);
		return s.substring(first, last);
	}

	public static Integer parseInteger(String token) {
		try {
			return Integer.parseInt(token);
		} catch (NumberFormatException e) {
			return null;
		}
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

	public static StringBuilder join(StringBuilder sb, Object array, int length, String... delimiters) {
		return join(sb, array, length, 1, maxDepthOf(array), null, delimiters);
	}

	public static StringBuilder join(StringBuilder sb, Object array, String... delimiters) {
		return join(sb, array, Array.getLength(array), delimiters);
	}

	public static <T> String join(Object array, int length, Function<T, String> mapper, String... delimiters) {
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

	public static String join(Collection<? extends Object> c, String... delimiters) {
		return join(c.toArray(), delimiters);
	}

	public static String[] split(StringTokenizer st, int nb) {
		return IntStream.range(0, nb).mapToObj(i -> st.nextToken()).toArray(String[]::new);
	}

	public static String[] split(StringTokenizer st) {
		return split(st, st.countTokens());
	}

	public static String getPathOf(String pathAndFileName) {
		int last = pathAndFileName.lastIndexOf("/");
		return last == -1 ? "" : pathAndFileName.substring(0, last + 1);
	}

	/**********************************************************************************************
	 * useful classes
	 *********************************************************************************************/

	public static class Contractor {
		private Map<IntArrayHashKey, int[]> map;

		private IntArrayHashKey hashKey;

		public Contractor() {
			map = new HashMap<IntArrayHashKey, int[]>(2000);
		}

		public void clear() {
			map.clear();
		}

		public void contract(int[][] m) {
			for (int i = 0; i < m.length; i++) {
				if (hashKey == null)
					hashKey = new IntArrayHashKey();
				hashKey.t = m[i];
				int[] t = map.get(hashKey);
				if (t == null) {
					map.put(hashKey, m[i]);
					hashKey = null;
				} else
					m[i] = t;
			}
		}

		public void contract(Collection<int[][]> collection) {
			for (int[][] m : collection)
				contract(m);
		}
	}

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

	public static class Stopwatch {

		private boolean cpuTimeSupported;
		private long startWallClockTime;

		/** Builds a stopwatch and starts it. */
		public Stopwatch() {
			cpuTimeSupported = ManagementFactory.getThreadMXBean().isCurrentThreadCpuTimeSupported();
			start();
		}

		private long computeCpuTime() {
			assert cpuTimeSupported;
			ThreadMXBean threads = ManagementFactory.getThreadMXBean();
			return Arrays.stream(threads.getAllThreadIds()).map(id -> threads.getThreadCpuTime(id)).sum();
			// return time; // ManagementFactory.getThreadMXBean().getCurrentThreadCpuTime();
		}

		public void start() {
			startWallClockTime = System.currentTimeMillis();
		}

		/** Returns the current duration given by the stopwatch while it is being currently running. */
		public long wckTime() {
			return System.currentTimeMillis() - startWallClockTime;
		}

		public String wckTimeInSeconds() {
			double l = (System.currentTimeMillis() - startWallClockTime) / 1000.0;
			return l < 10 ? df2.format(l) : df1.format(l);
		}

		/** Returns the cpu time in milliseconds */
		public long cpuTime() {
			return cpuTimeSupported ? computeCpuTime() / 1000000 : -1;
		}

		/** Returns the cpu time in seconds */
		public String cpuTimeInSeconds() {
			return cpuTimeSupported ? cpuTime() / 1000.0 + "" : "-1";
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

	/*
	 * This class allows to represent two integer values inside a single int or long value.
	 */
	public static final class CombinatorOfTwoInts {
		private final int maxLeftValue, maxRightValue;
		private final int offset; // used for managing pairs of values as a unique int
		private final long maxPossibleCombinedValue;

		public int leftValueIn(int combinedValue) {
			assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue;
			return combinedValue / offset;
		}

		public int rightValueIn(int combinedValue) {
			assert 0 <= combinedValue && combinedValue <= maxPossibleCombinedValue;
			return combinedValue % offset;
		}

		public int combinedIntValueFor(int leftValue, int rightValue) {
			assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue
					&& maxPossibleCombinedValue <= Integer.MAX_VALUE;
			return leftValue * offset + rightValue;
		}

		public long combinedLongValueFor(int leftValue, int rightValue) {
			assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
			return leftValue * offset + rightValue;
		}

		public long combinedMinMaxLongValueFor(int leftValue, int rightValue) {
			assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
			return (maxLeftValue - leftValue) * offset + rightValue;
		}

		public long combinedMaxMinLongValueFor(int leftValue, int rightValue) {
			assert 0 <= leftValue && leftValue <= maxLeftValue && 0 <= rightValue && rightValue <= maxRightValue;
			return leftValue * offset + (maxRightValue - rightValue);
		}

		public CombinatorOfTwoInts(int maxLeftValue, int maxRightValue) {
			this.maxLeftValue = maxLeftValue;
			this.maxRightValue = maxRightValue;
			Kit.control(0 < maxLeftValue && 0 < maxRightValue);
			this.offset = maxRightValue + 1;
			BigInteger b = (BigInteger.valueOf(maxLeftValue).multiply(BigInteger.valueOf(offset))).add(BigInteger.valueOf(maxRightValue));
			this.maxPossibleCombinedValue = b.longValueExact();
		}

		public CombinatorOfTwoInts(int maxRightValue) {
			this(Integer.MAX_VALUE - 1, maxRightValue);
		}

		public CombinatorOfTwoInts() {
			this(Integer.MAX_VALUE - 1, Integer.MAX_VALUE - 1);
		}
	}

	public static boolean useColors = true;

	public static final String BLACK = "\033[0;30m"; // BLACK
	public static final String YELLOW = "\u001b[33m"; // YELLOW
	public static final String CYAN = "\033[0;36m"; // CYAN
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
		try {
			return load(new FileInputStream(file), null); // no schema
		} catch (FileNotFoundException e) {
			return (Document) Kit.exit("File " + file.getName() + " does not exist", e);
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
		return (T[]) Utilities.collect(IVar.class, Stream.of(objects).map(o -> o instanceof XNode ? ((XNode) o).vars() : o));
	}

	public static int[] vals(Object... objects) {
		return Utilities.collectInt(objects);
	}

	// (3,-5) => -2; (3,10) => 3; (-3,-5) => 2; (-3,10) => -3; (3,0) => 0; (-3,0) => 0
	// 3y <= -5 => y <= -2; 3y <= 10 => y <= 3; -3y <= -5 => y >= 2; -3y <= 10 => y >= -3; 3y <= 0 => y <= 0; -3y <= 0 => y >= 0
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
	// 3y >= -5 => y >= -1; 3y >= 10 => y >= 4; -3y >= -5 => y <= 1; -3y >= 10 => y <= -4; 3y >= 0 => y>= 0; -3y >= 0 => y <= 0
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