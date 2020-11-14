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
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.lang.reflect.Array;
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

import org.xcsp.common.Utilities;

import dashboard.Arguments;
import executables.Resolution;

public final class Kit {
	private Kit() {
	}

	public static final DecimalFormat decimalFormat = new DecimalFormat("###.##", new DecimalFormatSymbols(Locale.ENGLISH));

	public static boolean[] toPrimitive(Stream<Boolean> stream) {
		Boolean[] t1 = stream.toArray(Boolean[]::new);
		boolean[] t2 = new boolean[t1.length];
		IntStream.range(0, t2.length).forEach(i -> t2[i] = t1[i]);
		return t2;
	}

	public static String dateOf(Class<?> clazz) {
		try {
			File f = new File(clazz.getResource(clazz.getSimpleName() + ".class").toURI());
			return new SimpleDateFormat("(dd MMM yyyy 'at' HH:mm)").format(f.lastModified()).toString();
		} catch (Exception e) {
			return "";
		}
	}

	public static int getPositionOfLastDigitAtHeadOf(String s) {
		return IntStream.range(0, s.length()).filter(i -> !Character.isDigit(s.charAt(i))).findFirst().orElse(s.length()) - 1;
	}

	public static String getTokenPossiblyRemovedFromHeadNumber(String s) {
		int pos = Kit.getPositionOfLastDigitAtHeadOf(s);
		return pos == -1 ? s : s.substring(pos + 1);
	}

	/**
	 * build an array of integers of the specified size where the values are randomly selected between 0 and nPossibleValues -1
	 */
	public static int[] pickDifferentValues(int length, int nPossibleValues, Random random) {
		assert length < nPossibleValues;
		if (length == 0)
			return new int[0];
		int[] source = Kit.range(nPossibleValues);
		int[] target = new int[length];
		for (int i = 0; i < length; i++) {
			int pos = random.nextInt(source.length - i);
			target[i] = source[pos];
			source[pos] = source[source.length - i - 1];
		}
		return Kit.sort(target);
	}

	public static Logger log = Logger.getLogger("Logger AbsCon");
	static {
		LogManager.getLogManager().reset();
		// Calendar c = Calendar.getInstance();
		Handler handler = new StreamHandler() {
			@Override
			public void publish(LogRecord record) {
				if (record.getLevel().intValue() < Level.INFO.intValue()) {
					if (Arguments.multiThreads)
						System.out.println("From " + ((Resolution) Thread.currentThread()).cp.settingsFilename + " :");
					System.out.println(record.getMessage());
				} else {
					if (Arguments.multiThreads)
						System.err.println("From " + ((Resolution) Thread.currentThread()).cp.settingsFilename + " :");
					// c.setTimeInMillis(record.getMillis());
					Thread t = Resolution.currentThread();
					if (t instanceof Resolution && !((Resolution) t).cp.settingXml.competitionMode)
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

	public static Object control(boolean conditionToBeRespected, Supplier<String> message) {
		return conditionToBeRespected ? null : exit(message.get(), new Exception());
	}

	public static Object control(boolean conditionToBeRespected) {
		return control(conditionToBeRespected, () -> "");
	}

	public static Object exit(String message, Throwable e) {
		if (!(Thread.currentThread() instanceof Resolution) || ((Resolution) Thread.currentThread()).cp.settingGeneral.makeExceptionsVisible)
			e.printStackTrace();
		System.out.println(message);
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

	public static final Comparator<byte[]> lexComparatorByte = (t1, t2) -> {
		for (int i = 0; i < t1.length; i++)
			if (t1[i] < t2[i])
				return -1;
			else if (t1[i] > t2[i])
				return +1;
		return 0;
	};

	public static final Comparator<short[]> lexComparatorShort = (t1, t2) -> {
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

	// public static final Comparator<int[]> lexComparatorInt = (t1, t2) -> {
	// for (int i = 0; i < t1.length; i++)
	// if (t1[i] < t2[i])
	// return -1;
	// else if (t1[i] > t2[i])
	// return +1;
	// return 0;
	// };
	//
	// public static final Comparator<String[]> lexComparatorString = (t1, t2) -> {
	// for (int i = 0; i < t1.length; i++) {
	// int res = t1[i].compareTo(t2[i]);
	// if (res != 0)
	// return res;
	// }
	// return 0;
	// };

	public static final Comparator<int[]> lexComparatorGeneral = (t1, t2) -> {
		for (int i = 0; i < t1.length; i++)
			if (i > t2.length - 1 || t1[i] > t2[i])
				return +1;
			else if (t1[i] < t2[i])
				return -1;
		return t1.length < t2.length ? -1 : 0;
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

	public static String getFirstLineIn(String fileName) {
		try (BufferedReader br = new BufferedReader(new FileReader(fileName))) {
			return br.readLine().trim();
		} catch (Exception e) {
			return (String) Kit.exit(e);
		}
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
		return Stream.of(t).anyMatch(v -> v == value);
	}

	public static <T> boolean isPresent(String s, String[][] m) {
		return Stream.of(m).anyMatch(t -> isPresent(s, t));
	}

	public static boolean isPresent(char value, char[]... m) {
		return Arrays.stream(m).anyMatch(t -> IntStream.range(0, t.length).anyMatch(i -> t[i] == value));
	}

	public static boolean isPresent(char value, String... t) {
		return Arrays.stream(t).anyMatch(s -> s.indexOf(value) != -1);
	}

	public static boolean isPresent(int value, int[] t) {
		return IntStream.of(t).anyMatch(v -> v == value);
	}

	public static boolean isPresent(int value, int[]... m) {
		return Stream.of(m).anyMatch(t -> isPresent(value, t));
	}

	// public static int indexOf(String s, String... t) {
	// return IntStream.range(0, t.length).filter(i -> t[i].equals(s)).findFirst().orElse(-1);
	// }
	//
	// public static int indexOf(String s, List<Object> list) {
	// return IntStream.range(0, list.size()).filter(i -> list.get(i).equals(s)).findFirst().orElse(-1);
	// }
	//
	// public static int indexOf(int value, int[] t) {
	// for (int i = 0; i < t.length; i++)
	// if (value == t[i])
	// return i;
	// return -1;
	// // return IntStream.range(0, t.length).filter(i -> t[i] == value).findFirst().orElse(-1);
	// }
	//
	// public static int indexOf(Object value, Object[] t) {
	// return IntStream.range(0, t.length).filter(i -> t[i] == value).findFirst().orElse(-1);
	// }

	public static boolean withOnly(int value, int[] t) {
		return IntStream.range(0, t.length).noneMatch(i -> t[i] != value);
	}

	public static boolean withNoNegativeValues(long[][] m) {
		return Stream.of(m).noneMatch(t -> Arrays.stream(t).anyMatch(v -> v < 0));
	}

	public static boolean allDifferentValues(int... t) {
		return IntStream.range(0, t.length).noneMatch(i -> IntStream.range(i + 1, t.length).anyMatch(j -> t[i] == t[j]));
	}

	// public static boolean withAllDifferentValues(int[] t, int except) {
	// return IntStream.range(0, t.length).noneMatch(i -> IntStream.range(i + 1, t.length).anyMatch(j -> t[i] == t[j] && t[i] != except));
	// }

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

	public static boolean isIncreasing(double[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] > t[i + 1]);
	}

	public static boolean isStrictlyIncreasing(int[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i] >= t[i + 1]);
	}

	public static <T extends Comparable<T>> boolean isStrictlyIncreasing(T[] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i].compareTo(t[i + 1]) >= 0);
	}

	public static boolean isLexIncreasing(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> Utilities.lexComparatorInt.compare(t[i], t[i + 1]) > 0);
	}

	public static boolean isLexStrictlyIncreasing(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> Utilities.lexComparatorInt.compare(t[i], t[i + 1]) >= 0);
	}

	public static boolean isLexStrictlyIncreasing(long[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> lexComparatorLong.compare(t[i], t[i + 1]) >= 0);
	}

	public static boolean isArrayOnlyContainingTuplesWithSameSize(int[][] t) {
		return IntStream.range(0, t.length - 1).noneMatch(i -> t[i].length != t[i + 1].length);
	}

	public static boolean isPrefix(int[] t1, int[] t2) {
		return t1.length <= t2.length && IntStream.range(0, t1.length).noneMatch(i -> t1[i] != t2[i]);
	}

	public static boolean isSubtuple(int[] subtuple, int[] tuple, int from) {
		return from + subtuple.length < tuple.length && IntStream.range(0, subtuple.length).noneMatch(i -> subtuple[i] != tuple[from + i]);
	}

	public static int countIn(char c, String s) {
		return IntStream.range(0, s.length()).filter(i -> s.charAt(i) == c).map(i -> 1).sum();
	}

	public static int countIn(int value, int[] t) {
		return Arrays.stream(t).filter(v -> v == value).map(v -> 1).sum();
	}

	public static int countIn(int value, int[] t, int from, int to) {
		return IntStream.range(from, to).filter(i -> t[i] == value).map(i -> 1).sum();
	}

	public static int countIn(boolean value, boolean[] t) {
		return IntStream.range(0, t.length).filter(i -> t[i] == value).map(i -> 1).sum();
	}

	public static int[][] appendTuple(int[][] t, int... tuple) {
		int[][] tt = new int[t.length + 1][];
		System.arraycopy(t, 0, tt, 0, t.length);
		tt[t.length] = tuple;
		return tt;
	}

	public static int[][] appendTuples(int[][] t, int[]... tuples) {
		int[][] tt = new int[t.length + tuples.length][];
		System.arraycopy(t, 0, tt, 0, t.length);
		for (int i = 0; i < tuples.length; i++)
			tt[t.length + i] = tuples[i];
		return tt;
	}

	public static int[][] cartesianProduct(int[] t1, int... t2) {
		int[][] tt = new int[t1.length * t2.length][];
		for (int i = 0; i < t1.length; i++)
			for (int j = 0; j < t2.length; j++)
				tt[i * t2.length + j] = new int[] { t1[i], t2[j] };
		return tt;
	}

	public static long sum(int[] t, int from) {
		return IntStream.range(from, t.length).map(i -> t[i]).sum();
	}

	public static long sum(int[] t) {
		return sum(t, 0);
	}

	public static long sum(int[][] m) {
		return Stream.of(m).mapToLong(t -> sum(t)).sum();
	}

	public static long weightedSum(int[] t, int[] coeffs) {
		assert t.length == coeffs.length;
		// note that no overflow control is performed here
		long sum = 0;
		for (int i = 0; i < t.length; i++)
			sum += coeffs[i] * t[i];
		return sum;
	}

	public static final long addSafe(long left, long right) {
		if (right > 0 ? left > Long.MAX_VALUE - right : left < Long.MIN_VALUE - right)
			Kit.exit("pb overflow " + left + " " + right);
		return left + right;
	}

	public static double computeAnp(int n, int p) {
		Kit.control(n >= p);
		double d = 1;
		for (int i = n; i > n - p; i--)
			d *= i;
		return d;
	}

	public static double computeCnp(int n, int p) {
		double d = computeAnp(n, p);
		for (int i = 2; i <= p; i++)
			d /= i;
		return d;
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

	public static int[] buildMapping(int[] src, int[] dst) {
		int[] mapping = new int[src.length];
		for (int i = 0; i < src.length; i++)
			mapping[i] = Utilities.indexOf(src[i], dst);
		return mapping;
	}

	public static int[] buildMapping(Object[] src, Object[] dst) {
		int[] mapping = new int[src.length];
		for (int i = 0; i < src.length; i++)
			mapping[i] = Utilities.indexOf(src[i], dst);
		return mapping;
	}

	public static int[] buildPermutation(Random random, int size) {
		int[] values = Kit.range(size);
		int[] t = new int[size];
		for (int i = 0; i < size; i++) {
			int j = random.nextInt(size - i);
			t[i] = values[j];
			values[j] = values[size - i - 1];
		}
		return t;
	}

	public static int[] mapTuple(int[] src, int[] dst, int[] mapping) {
		for (int i = 0; i < Math.min(dst.length, mapping.length); i++)
			dst[i] = src[mapping[i]];
		return dst;
	}

	public static int[] mapTuple(int[] src, int[] mapping) {
		return mapTuple(src, src.clone(), mapping);
	}

	public static long[] mapTuple(long[] src, long[] dst, int[] mapping) {
		for (int i = 0; i < Math.min(dst.length, mapping.length); i++)
			dst[i] = src[mapping[i]];
		return dst;
	}

	public static long[] mapTuple(long[] src, int[] mapping) {
		return mapTuple(src, src.clone(), mapping);
	}

	public static long[][] mapTuples(long[][] src, int[] mapping) {
		return Stream.of(src).map(t -> mapTuple(t, mapping)).toArray(long[][]::new);
	}

	public static String transformThroughMap(String s, Map<String, String> map) {
		StringBuilder sb = new StringBuilder();
		StringTokenizer st = new StringTokenizer(s);
		while (st.hasMoreTokens()) {
			String token = st.nextToken();
			String newToken = map.get(token);
			sb.append(newToken == null ? token : newToken);
			if (st.hasMoreTokens())
				sb.append(" ");
		}
		return sb.toString();
	}

	public static int[] buildReverseMapping(int[] mapping) {
		int[] reverseMapping = new int[mapping.length];
		for (int i = 0; i < reverseMapping.length; i++)
			reverseMapping[mapping[i]] = i;
		return reverseMapping;
	}

	public static boolean areMappedTuples(int[] tuple1, int[] tuple2, int[][] mapping) {
		return Stream.of(mapping).noneMatch(t -> tuple1[t[0]] != tuple2[t[1]]);
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

	public static int[] reverse(int[] t) {
		for (int i = 0; i < t.length / 2; i++) {
			int tmp = t[i];
			t[i] = t[t.length - i - 1];
			t[t.length - i - 1] = tmp;
		}
		return t;
	}

	public static long[] reverse(long[] t) {
		for (int i = 0; i < t.length / 2; i++) {
			long tmp = t[i];
			t[i] = t[t.length - i - 1];
			t[t.length - i - 1] = tmp;
		}
		return t;
	}

	public static boolean selectInDirectory(List<String> list, File dir, int limit, FileFilter fileFilter) {
		// String[] listDirectory = Stream.of(Kit.sort(dir.list())).map(s -> new File(dir, s)).filter(f -> f.isFile() &&
		// fileFilter.accept(f))
		// .map(f -> f.getAbsolutePath()).limit(limit).toArray(String[]::new); / NOT CORRECT
		// if (listDirectory.length == limit) return true;
		String[] listDirectory = Kit.sort(dir.list());
		for (String s : listDirectory) {
			File f = new File(dir, s);
			if (f.isFile() && fileFilter.accept(f)) {
				list.add(f.getAbsolutePath());
				if (list.size() >= limit)
					return true;
			}
		}
		return Stream.of(listDirectory).map(s -> new File(dir, s)).anyMatch(f -> f.isDirectory() && selectInDirectory(list, f, limit, fileFilter));
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

	public static String getFormattedCurrentDate() {
		Calendar c = new GregorianCalendar();
		c.setTimeInMillis(System.currentTimeMillis());
		int year = c.get(Calendar.YEAR), month = c.get(Calendar.MONTH), day = c.get(Calendar.DAY_OF_MONTH), hour = c.get(Calendar.HOUR_OF_DAY),
				minute = c.get(Calendar.MINUTE);
		DecimalFormat df = new DecimalFormat("00");
		return year + "_" + df.format(month) + "_" + df.format(day) + "_" + df.format(hour) + "_" + df.format(minute);
	}

	public static String getFormattedMemorySize(long size) {
		long m = size / 1000000, k = size / 1000 - m * 1000;
		return m + "M" + k;
	}

	public static long getUsedMemory() {
		Runtime rt = Runtime.getRuntime();
		return rt.totalMemory() - rt.freeMemory();
	}

	public static String getFormattedUsedMemorySize() {
		return getFormattedMemorySize(getUsedMemory());
	}

	public static void copy(int[] src, int[] dst) {
		for (int i = dst.length - 1; i >= 0; i--)
			dst[i] = src[i];
	}

	public static final <T> int[][] mappingBetween(T[] t1, T[] t2) {
		return IntStream.range(0, t1.length).mapToObj(i -> new int[] { i, Utilities.indexOf(t1[i], t2) }).filter(t -> t[1] != -1).toArray(int[][]::new);
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

	/**
	 * Replaces all occurrences of the given old char with the given new char. This method is used as the standard method of the String class do not behave
	 * correctly for some characters.
	 */
	public static String replaceAll(String s, char oldChar, char newChar) {
		StringBuilder sb = new StringBuilder(s);
		for (int i = 0; i < sb.length(); i++)
			if (sb.charAt(i) == oldChar)
				sb.setCharAt(i, newChar);
		return sb.toString();
	}

	public static String getPathOf(String pathAndFileName) {
		int last = pathAndFileName.lastIndexOf("/");
		return last == -1 ? "" : pathAndFileName.substring(0, last + 1);
	}

	public static double[] computeQuantileOf(double[] t, int nbIntervals, boolean mustBeSorted) {
		double[] tt = mustBeSorted ? Kit.sort(t.clone()) : t;
		assert Kit.isIncreasing(tt);
		return IntStream.range(0, nbIntervals - 1).mapToDouble(i -> tt[(int) Math.ceil(((i + 1) * tt.length) / (double) nbIntervals) - 1]).toArray();
	}

	public static int computeMaxOf(int[] t) {
		return Arrays.stream(t).max().orElse(Integer.MIN_VALUE);
	}

	public static long computeMaxOf(long[] t) {
		return Arrays.stream(t).max().orElse(Long.MIN_VALUE);
	}

	public static int computeMaxOf(int[][] m) {
		return Stream.of(m).mapToInt(t -> computeMaxOf(t)).max().orElse(Integer.MIN_VALUE);
	}

	public static double computeAveragePositionOf(int[] t) {
		int nbElements = 0;
		long sum = 0;
		for (int i = 0; i < t.length; i++) {
			nbElements += t[i];
			sum += t[i] * i;
		}
		return nbElements == 0 ? -1 : sum / (double) nbElements;
	}

	public static double computeVarianceOf(double[] t) {
		double sum = Arrays.stream(t).sum();
		double average = sum / t.length;
		double gapSum = Arrays.stream(t).map(d -> (d - average) * (d - average)).sum();
		return gapSum / t.length;
	}

	public static int[] computePrimes(int limitIncluded) {
		Boolean[] primes = IntStream.range(0, limitIncluded + 1).mapToObj(i -> i < 2 ? Boolean.FALSE : Boolean.TRUE).toArray(Boolean[]::new);
		return IntStream.range(2, limitIncluded + 1).filter(i -> primes[i]).map(i -> {
			for (int j = i * 2; j < primes.length; j = j + i)
				primes[j] = false;
			return i;
		}).toArray();
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

	public static DecimalFormatSymbols symbols = new DecimalFormatSymbols(Locale.US);
	public static DecimalFormat df2 = new DecimalFormat("0.00", symbols);
	public static DecimalFormat df1 = new DecimalFormat("0.0", symbols);

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
}