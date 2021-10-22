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

import sets.SetDense;

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

	public static void or(long[] inout, long[] in, SetDense set) {
		int[] dense = set.dense;
		if (inout.length != in.length) { // mask compression mode used for 'in'
			for (int i = set.limit; i >= 0; i--) {
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
			for (int i = set.limit; i >= 0; i--) {
				int j = dense[i];
				inout[j] |= in[j];
			}
		}
	}

	public static void orInverse(long[] inout, long[] in, SetDense set) {
		int[] dense = set.dense;
		if (inout.length != in.length) { // mask compression mode used for in
			for (int i = set.limit; i >= 0; i--) {
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
			for (int i = set.limit; i >= 0; i--) {
				int j = dense[i];
				inout[j] |= ~in[j];
			}
		}
	}

	public static void and(long[] inout, long[] in, SetDense set) {
		int[] dense = set.dense;
		for (int i = set.limit; i >= 0; i--) {
			int j = dense[i];
			inout[j] &= in[j];
		}
	}

	public static int firstNonNullWord(long[] t1, long[] t2, SetDense set) {
		int[] dense = set.dense;
		if (t1.length != t2.length) { // mask compression mode used for t2
			for (int i = set.limit; i >= 0; i--) {
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
		} else { // non mask compression mode
			for (int i = set.limit; i >= 0; i--) {
				int j = dense[i];
				if ((t1[j] & t2[j]) != 0L)
					return j;
			}
		}
		return -1;
	}

	public static int firstErasingWord(long[] t1, long[] t2, SetDense set) {
		int[] dense = set.dense;
		for (int i = set.limit; i >= 0; i--) {
			int j = dense[i];
			if ((t1[j] & t2[j]) != t1[j])
				return j;
		}
		return -1;
	}

	/**
	 * Inverses all bits of the specified bit vector, when only considering the long at the specified positions (given
	 * by the specified dense set)
	 * 
	 * @param inout
	 *            a bit vector defined by the sequence of bits over an array of long
	 * @param set
	 *            a dense set with positions of long for the bit vector
	 * @return the same bit vector (after inversion)
	 */
	public static long[] inverse(long[] inout, SetDense set) {
		int[] dense = set.dense;
		for (int i = set.limit; i >= 0; i--) {
			int j = dense[i];
			inout[j] = ~inout[j];
		}
		return inout;
	}

	/**
	 * Counts and returns the number of bits at 1 in the specified bit vector
	 * 
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of long
	 * @return the number of bits at 1 in the specified bit vector
	 */
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

	/**
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of longs
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 * @return true if in the specified bit vector the bit at the specified position is 1
	 */
	public static boolean isPresent(long[] t, int bitPosition) {
		return (t[bitPosition / Long.SIZE] & ONE_LONG_BIT_TO_1[bitPosition % Long.SIZE]) != 0; // ALL_LONG_BITS_TO_0;
	}

	/**
	 * @param bitPosition
	 *            the position of a bit in the bit vector (long)
	 * @return a bit vector (long) defined by a sequence of 1 followed by a sequence of 0 from the specified position
	 */
	public static long bitsAt1To(int bitPosition) {
		long v = 0;
		for (int i = 0; i < bitPosition; i++)
			v |= ONE_LONG_BIT_TO_1[i];
		return v;
	}

	/**
	 * @param bitPosition
	 *            the position of a bit in the bit vector (long)
	 * @return a bit vector (long) defined by a sequence of 0 followed by a sequence of 1 from the specified position
	 */
	public static long bitsAt1From(int bitPosition) {
		long v = 0;
		for (int i = bitPosition; i < 64; i++)
			v |= ONE_LONG_BIT_TO_1[i];
		return v;
	}

	/**
	 * Sets to 0 the bit at the specified position of the specified bit vector
	 * 
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of bytes
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 */
	public static void setTo0(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		t[bytePosition] &= ONE_BYTE_BIT_TO_0[bitPosition % 8];
	}

	/**
	 * Sets to 1 the bit at the specified position of the specified bit vector
	 * 
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of bytes
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 */
	public static void setTo1(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		t[bytePosition] |= ONE_BYTE_BIT_TO_1[bitPosition % 8];
	}

	/**
	 * Sets to 0 the bit at the specified position of the specified bit vector
	 * 
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of longs
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 */
	public static void setTo0(long[] t, int bitPosition) {
		int bytePosition = bitPosition / 64;
		t[bytePosition] &= ONE_LONG_BIT_TO_0[bitPosition % 64];
	}

	/**
	 * Sets to 1 the bit at the specified position of the specified bit vector
	 * 
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of longs
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 */
	public static void setTo1(long[] t, int bitPosition) {
		int bytePosition = bitPosition / 64;
		t[bytePosition] |= ONE_LONG_BIT_TO_1[bitPosition % 64];
	}

	/**
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of bytes
	 * @param bitPosition
	 *            the position of a bit in the bit vector
	 * @return true is the bit at the specified position is 1 in the specified bit vector
	 */
	public static boolean isAt1(byte[] t, int bitPosition) {
		int bytePosition = bitPosition / 8;
		return (t[bytePosition] & ONE_BYTE_BIT_TO_1[bitPosition % 8]) != 0;
	}

	/**
	 * Returns a string of the specified length (or 64 if length >= 64) forming a sequence of 0 and 1 corresponding to
	 * the specified long
	 * 
	 * @param v
	 *            a long, seen as a sequence of 64 bits
	 * @param length
	 *            the length of the string to be built
	 * @return a string forming a sequence of 0 and 1
	 */
	private static String decrypt(long v, int length) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < length; i++)
			sb.append(((v & ONE_LONG_BIT_TO_1[i]) != 0) ? "1" : "0");
		return sb.toString();
	}

	/**
	 * Returns a string forming a sequence of 0 and 1 corresponding to the specified long
	 * 
	 * @param v
	 *            a long, seen as a sequence of 64 bits
	 * @return a string forming a sequence of 0 and 1
	 */
	public static String decrypt(long v) {
		return decrypt(v, Long.SIZE);
	}

	/**
	 * Returns a string of the specified length (or 64*t.length if length >= 64*t.length) forming a sequence of 0 and 1
	 * corresponding to the specified array of long
	 * 
	 * @param t
	 *            an array of long, seen as sequences of 64 bits
	 * @param length
	 *            the length of the string to be built
	 * @return a string forming a sequence of 0 and 1
	 */
	public static String decrypt(long[] t, int length) {
		StringBuilder sb = new StringBuilder();
		for (long l : t) {
			if (length <= 0)
				break;
			sb.append(decrypt(l, Math.min(length, Long.SIZE))).append(' ');
			length -= Long.SIZE;
		}
		return sb.toString();
	}

	/**
	 * Returns a string forming a sequence of 0 and 1 corresponding to the specified array of long
	 * 
	 * @param t
	 *            an array of long, seen as sequences of 64 bits
	 * @return a string forming a sequence of 0 and 1
	 */
	public static String decrypt(long[] t) {
		return decrypt(t, Integer.MAX_VALUE);
	}

	public static int convert(int v, int nBytesToCopy, byte[] buffer, int position) {
		for (int i = 0; i < nBytesToCopy; i++) {
			buffer[position++] = (byte) v;
			v = v >> Byte.SIZE;
		}
		return position;
	}

	public static int convert(long[] t, int nBitsToCopy, byte[] buffer, int position) {
		for (long l : t) {
			for (int cnt = 0; cnt < 8; cnt++) {
				if (nBitsToCopy <= 0)
					return position;
				buffer[position++] = (byte) l;
				l = l >> Byte.SIZE;
				nBitsToCopy -= Byte.SIZE;
			}
		}
		return position;
	}

	public static void main(String[] args) {
		long[] t1 = { 4532, -65, 900 }, t2 = { 4532, 675, -900 };
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
