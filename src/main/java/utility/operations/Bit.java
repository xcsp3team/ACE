/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility.operations;

import utility.sets.SetDense;

public final class Bit {

	public static final short ALL_SHORT_BITS_TO_1 = -1;

	public static final int ALL_INT_BITS_TO_1 = -1; // 0xFFFFFFFF;

	public static final long ALL_LONG_BITS_TO_1 = -1; // 0xFFFFFFFFFFFFFFFFL;

	public static final byte[] ONE_BYTE_BIT_TO_0 = buildOneByteBitTo0();

	public static final int[] ONE_INT_BIT_TO_0 = buildOneIntBitTo0();

	public static final long[] ONE_LONG_BIT_TO_0 = buildOneLongBitTo0();

	public static final byte[] ONE_BYTE_BIT_TO_1 = buildOneByteBitTo1();

	public static final short[] ONE_SHORT_BIT_TO_1 = buildOneShortBitTo1();

	public static final int[] ONE_INT_BIT_TO_1 = buildOneIntBitTo1();

	public static final long[] ONE_LONG_BIT_TO_1 = buildOneLongBitTo1();

	private static byte[] buildOneByteBitTo0() {
		byte[] t = new byte[8];
		t[7] = 0x7F;
		byte current = (byte) 0xBF;
		for (int i = 6; i >= 0; i--) {
			t[i] = current;
			current = (byte) (current >> 1);
		}
		return t;
	}

	private static int[] buildOneIntBitTo0() {
		int[] t = new int[32];
		t[31] = 0x7FFFFFFF;
		int current = 0xBFFFFFFF;
		for (int i = 30; i >= 0; i--) {
			t[i] = current;
			current = current >> 1;
		}
		return t;
	}

	private static long[] buildOneLongBitTo0() {
		long[] t = new long[64];
		t[63] = 0x7FFFFFFFFFFFFFFFL;
		long current = 0xBFFFFFFFFFFFFFFFL;
		for (int i = 62; i >= 0; i--) {
			t[i] = current;
			current = current >> 1;
		}
		return t;
	}

	private static byte[] buildOneByteBitTo1() {
		byte[] t = new byte[8];
		byte current = 0x01;
		for (int i = 0; i < t.length; i++) {
			t[i] = current;
			current = (byte) (current << 1);
		}
		return t;
	}

	private static short[] buildOneShortBitTo1() {
		short[] t = new short[16];
		short current = 0x0001;
		for (int i = 0; i < t.length; i++) {
			t[i] = current;
			current = (short) (current << 1);
		}
		return t;
	}

	private static int[] buildOneIntBitTo1() {
		int[] t = new int[32];
		int current = 0x00000001;
		for (int i = 0; i < t.length; i++) {
			t[i] = current;
			current = current << 1;
		}
		return t;
	}

	private static long[] buildOneLongBitTo1() {
		long[] t = new long[64];
		long current = 0x0000000000000001L;
		for (int i = 0; i < t.length; i++) {
			t[i] = current;
			current = current << 1;
		}
		return t;
	}

	/**
	 * Is t1 included in t2 (considering that each bit represents an element of a set)?
	 */
	public static boolean isIncluded(long[] t1, long[] t2) {
		assert t1.length == t2.length;
		for (int i = 0; i < t1.length; i++)
			if ((t1[i] | t2[i]) != t2[i])
				return false;
		return true;
	}

	public static int firstPositionOfNonInclusion(long[] t1, long[] t2) {
		assert t1.length == t2.length;
		int position = 0;
		for (int i = 0; i < t1.length; i++) {
			if ((t1[i] | t2[i]) != t2[i]) {
				long l1 = t1[i], l2 = t2[i];
				for (int j = 0; j < 64; j++)
					if ((l1 & ONE_LONG_BIT_TO_1[j]) == 0)
						continue;
					else if ((l2 & ONE_LONG_BIT_TO_1[j]) == 0)
						return position + j;
			}
			position += 64;
		}
		return -1;
	}

	public static boolean nonNullIntersection2(long[] t1, long[] t2, int j) {
		if (t1.length != t2.length) { // mask compression mode used for t2
			if (t2[1] == 0L) {
				for (int k = 2; k < t2.length; k += 2)
					if (t2[k] == j)
						return (t1[j] & t2[k + 1]) != 0L;
					else if (t2[k] > j)
						break;
			} else {
				for (int k = t2.length - 2; k >= 2; k -= 2)
					if (t2[k] == j) {
						return (t1[j] & t2[k + 1]) != 0L;
					} else if (t2[k] < j)
						break;
			}
			return (t1[j] & t2[0]) != 0L;
		}
		return (t1[j] & t2[j]) != 0L;
	}

	// public static void or(long[] inout, long[] in, SetDense dset) {
	// int[] dense = dset.dense;
	// for (int i = dset.limit; i >= 0; i--) {
	// int j = dense[i];
	// inout[j] |= in[j];
	// }
	// }

	public static void or2(long[] inout, long[] in, SetDense dset) {
		int[] dense = dset.dense;
		if (inout.length != in.length) { // mask compression mode used for 'in'
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				boolean found = false;
				if (in[1] == 0L) {
					for (int k = 2; !found && k < in.length; k += 2)
						if (in[k] == j) {
							inout[j] |= in[k + 1];
							found = true;
						} else if (in[k] > j)
							break;
				} else {
					for (int k = in.length - 2; !found && k >= 2; k -= 2)
						if (in[k] == j) {
							inout[j] |= in[k + 1];
							found = true;
						} else if (in[k] < j)
							break;
				}
				if (!found)
					inout[j] |= in[0]; // default word
			}
		} else { // non mask compression mode
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				inout[j] |= in[j];
			}
		}
	}

	// public static void orInverse(long[] inout, long[] in, SetDense dset) {
	// int[] dense = dset.dense;
	// for (int i = dset.limit; i >= 0; i--) {
	// int j = dense[i];
	// inout[j] |= ~in[j];
	// }
	// }

	public static void orInverse2(long[] inout, long[] in, SetDense dset) {
		int[] dense = dset.dense;
		if (inout.length != in.length) { // mask compression mode used for in
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				boolean found = false;
				if (in[1] == 0L) {
					for (int k = 2; !found && k < in.length; k += 2)
						if (in[k] == j) {
							inout[j] |= ~in[k + 1];
							found = true;
						} else if (in[k] > j)
							break;
				} else {
					for (int k = in.length - 2; !found && k >= 2; k -= 2)
						if (in[k] == j) {
							inout[j] |= ~in[k + 1];
							found = true;
						} else if (in[k] < j)
							break;
				}
				if (!found)
					inout[j] |= ~in[0]; // default word
			}
		} else { // non mask compression mode
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				inout[j] |= ~in[j];
			}
		}
	}

	public static void and(long[] inout, long[] in, SetDense dset) {
		int[] dense = dset.dense;
		for (int i = dset.limit; i >= 0; i--) {
			int j = dense[i];
			inout[j] &= in[j];
		}
	}

	// public static int firstNonNullWord(long[] t1, long[] t2, SetDense dset) {
	// int[] dense = dset.dense;
	// for (int i = dset.limit; i >= 0; i--) {
	// int j = dense[i];
	// if ((t1[j] & t2[j]) != 0L)
	// return j;
	// }
	// return -1;
	// }

	public static int firstNonNullWord2(long[] t1, long[] t2, SetDense dset) {
		int[] dense = dset.dense;
		if (t1.length != t2.length) { // mask compression mode used for t2
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				boolean found = false;
				if (t2[1] == 0L) {
					for (int k = 2; !found && k < t2.length; k += 2)
						if (t2[k] == j) {
							if ((t1[j] & t2[k + 1]) != 0L)
								return j;
							found = true;
						} else if (t2[k] > j)
							break;
				} else {
					for (int k = t2.length - 2; !found && k >= 2; k -= 2)
						if (t2[k] == j) {
							if ((t1[j] & t2[k + 1]) != 0L)
								return j;
							found = true;
						} else if (t2[k] < j)
							break;
				}
				if (!found)
					if ((t1[j] & t2[0]) != 0L)
						return j;
			}
			return -1;
		} else {
			for (int i = dset.limit; i >= 0; i--) {
				int j = dense[i];
				if ((t1[j] & t2[j]) != 0L)
					return j;
			}
			return -1;
		}
	}

	public static int firstErasingWord(long[] t1, long[] t2, SetDense dset) {
		int[] dense = dset.dense;
		for (int i = dset.limit; i >= 0; i--) {
			int j = dense[i];
			if ((t1[j] & t2[j]) != t1[j]) {
				// System.out.println(dset.limit() - i);
				return j;
			}
		}
		return -1;
	}

	public static long[] inverse(long[] inout) {
		for (int i = 0; i < inout.length; i++)
			inout[i] = ~inout[i];
		return inout;
	}

	public static long[] inverse(long[] inout, SetDense dset) {
		int[] dense = dset.dense;
		for (int i = dset.limit; i >= 0; i--) {
			int j = dense[i];
			inout[j] = ~inout[j];
		}
		return inout;
	}

	public static long[] inverse(long[] out, long[] in) {
		for (int i = 0; i < in.length; i++)
			out[i] = ~in[i];
		return out;
	}

	public static long[] inverse(long[] out, long[] in, SetDense dset) {
		int[] dense = dset.dense;
		for (int i = dset.limit; i >= 0; i--) {
			int j = dense[i];
			out[j] = ~in[j];
		}
		return out;
	}

	public static int count1(long[] t) {
		int cnt = 0;
		for (int i = 0; i < t.length; i++)
			cnt += Long.bitCount(t[i]);
		return cnt;
	}

	public static int firstZeroIn(long[] t) {
		int position = 0;
		for (int i = 0; i < t.length; i++) {
			if ((ALL_LONG_BITS_TO_1 & t[i]) != ALL_LONG_BITS_TO_1) {
				long l = t[i];
				for (int j = 0; j < 64; j++)
					if ((l & ONE_LONG_BIT_TO_1[j]) == 0)
						return position + j;
			}
			position += 64;
		}
		return -1;
	}

	public static boolean isPresent(long[] t, int idx) {
		return (t[idx / Long.SIZE] & ONE_LONG_BIT_TO_1[idx % Long.SIZE]) != 0; // ALL_LONG_BITS_TO_0;
	}

	public static long bitsA1To(int limit) {
		long v = 0;
		for (int i = 0; i < limit; i++)
			v |= ONE_LONG_BIT_TO_1[i];
		return v;
	}

	public static long bitsAt1From(int from) {
		long v = 0;
		for (int i = from; i < 64; i++)
			v |= ONE_LONG_BIT_TO_1[i];
		return v;
	}

	public static void setTo0(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		t[bytePosition] &= ONE_BYTE_BIT_TO_0[bitPosition % 8];
	}

	public static void setTo1(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		t[bytePosition] |= ONE_BYTE_BIT_TO_1[bitPosition % 8];
	}

	public static void setTo0(long[] t, int bitPosition) {
		int bytePosition = bitPosition / 64;
		t[bytePosition] &= ONE_LONG_BIT_TO_0[bitPosition % 64];
	}

	public static void setTo1(long[] t, int bitPosition) {
		int bytePosition = bitPosition / 64;
		t[bytePosition] |= ONE_LONG_BIT_TO_1[bitPosition % 64];
	}

	public static boolean isAt1(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		return (t[bytePosition] & ONE_BYTE_BIT_TO_1[bitPosition % 8]) != 0;
	}

	public static String decrypt(long v, int limit) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < limit; i++)
			sb.append(((v & ONE_LONG_BIT_TO_1[i]) != 0) ? "1" : "0");
		return sb.toString();
	}

	public static String decrypt(long v) {
		return decrypt(v, Long.SIZE);
	}

	public static String decrypt(long[] t, int globalLimit) {
		StringBuilder sb = new StringBuilder();
		for (long l : t) {
			if (globalLimit <= 0)
				break;
			sb.append(decrypt(l, Math.min(globalLimit, Long.SIZE))).append(' ');
			globalLimit -= 64;
		}
		return sb.toString();
	}

	public static String decrypt(long[] t) {
		return decrypt(t, Integer.MAX_VALUE);
	}

	public static int convert(int v, int nBytesToCopy, byte[] buffer, int position) {
		for (int i = 0; i < nBytesToCopy; i++) {
			buffer[position++] = (byte) v;
			v = v >> 8;
		}
		return position;
	}

	public static int convert(long[] t, int nBitsToCopy, byte[] buffer, int position) {
		for (long l : t) {
			for (int cnt = 0; cnt < 8; cnt++) {
				if (nBitsToCopy <= 0)
					return position;
				buffer[position++] = (byte) l;
				l = l >> 8;
				nBitsToCopy -= 8;
			}
		}
		return position;
	}

	public static void main(String[] args) {
		long[] t1 = { 4532, -65, 900 };
		long[] t2 = { 4532, 675, -900 };
		System.out.println(decrypt(t1, 115));
		System.out.println(decrypt(t2, 115));
		System.out.println(firstPositionOfNonInclusion(t1, t2));
	}
}

// public static int copy(long[] t, int nbBitsToCopy, byte[] buffer, int globalFirstFreeBitPosition) {
// int bytePosition = globalFirstFreeBitPosition / 8;
// int bitPosition = globalFirstFreeBitPosition % 8;
// int hole = (bitPosition == 0 ? 0 : 8 - bitPosition);
//
// if (nbBitsToCopy <= hole) {
// buffer[bytePosition] = (byte) (buffer[bytePosition] | (byte) (t[0] << bitPosition));
// return globalFirstFreeBitPosition + nbBitsToCopy;
// }
// int i = 0, j = 0;
// long l = 0;
// boolean fullByteCopyfinished = false;
// for (; !fullByteCopyfinished && i < t.length; i++) {
// l = t[i];
// for (j = 0; !fullByteCopyfinished && j < 8; j++) {
// if (nbBitsToCopy <= 8 + hole)
// fullByteCopyfinished = true;
// buffer[bytePosition++] = (byte) l;
// l = l >> 8;
// nbBitsToCopy -= 8;
// }
// }
// // int nbCopiedBytes = bytePosition - globalFirstFreeBitPosition / 8;
// bytePosition = globalFirstFreeBitPosition / 8;
// buffer[bytePosition] = (byte) (buffer[bytePosition] | (byte) (l << bitPosition));
// nbBitsToCopy -= hole;
// return 0;
// }
