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

/**
 * This class contains various methods on bit vectors.
 * 
 * @author Christophe Lecoutre
 */
public final class Bit {

	/**
	 * A word (long) with only bits set to 1
	 */
	public static final long ALL_LONG_BITS_TO_1 = -1; // 0xFFFFFFFFFFFFFFFFL;

	/**
	 * ONE_BYTE_BIT_TO_0[i] is a word (byte) with only one bit to 0, the one at index i
	 */
	private static final byte[] ONE_BYTE_BIT_TO_0 = buildOneByteBitTo0();

	/**
	 * ONE_LONG_BIT_TO_0[i] is a word (long) with only one bit to 0, the one at index i
	 */
	public static final long[] ONE_LONG_BIT_TO_0 = buildOneLongBitTo0();

	/**
	 * ONE_BYTE_BIT_TO_1[i] is a word (long) with only one bit to 1, the one at index i
	 */
	private static final byte[] ONE_BYTE_BIT_TO_1 = buildOneByteBitTo1();

	/**
	 * ONE_LONG_BIT_TO_1[i] is a word (long) with only one bit to 1, the one at index i
	 */
	public static final long[] ONE_LONG_BIT_TO_1 = buildOneLongBitTo1();

	private static byte[] buildOneByteBitTo0() {
		byte[] t = new byte[8];
		t[7] = 0x7F; // 0x7FFFFFFF for int
		byte current = (byte) 0xBF; // 0xBFFFFFFF for int
		for (int i = 6; i >= 0; i--) {
			t[i] = current;
			current = (byte) (current >> 1);
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
		byte current = 0x01; // 0x0001 for short and 0x00000001 for int
		for (int i = 0; i < t.length; i++) {
			t[i] = current;
			current = (byte) (current << 1);
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
	 * @param t1
	 *            a first bit vector defined by the sequence of bits over an array of long
	 * @param t2
	 *            a second bit vector defined by the sequence of bits over an array of long
	 * @return the first index of a bit at 1 in t1 and at 0 in t2, or -1 if no such index exists
	 */
	public static int firstNonInclusionIndex(long[] t1, long[] t2) {
		assert t1.length == t2.length;
		int position = 0;
		for (int i = 0; i < t1.length; i++) {
			if ((t1[i] | t2[i]) != t2[i]) {
				long l1 = t1[i], l2 = t2[i];
				for (int j = 0; j < 64; j++)
					if ((l1 & ONE_LONG_BIT_TO_1[j]) == 0)
						continue; // because 0 in l1
					else if ((l2 & ONE_LONG_BIT_TO_1[j]) == 0)
						return position + j;
			}
			position += 64;
		}
		return -1;
	}

	/**
	 * Returns true if the intersection of the two words of the specified bit vectors at the specified index is 0.
	 * Possibly, mask compression may have been used for the second bit vector.
	 * 
	 * @param t1
	 *            a first bit vector defined by the sequence of bits over an array of long
	 * @param t2
	 *            a second bit vector defined by the sequence of bits over an array of long
	 * @param i
	 *            the index of a word (long)
	 * @return true if the intersection of the two words of the specified bit vectors at the specified index is 0
	 */
	public static boolean nullIntersection(long[] t1, long[] t2, int i) {
		if (t1.length != t2.length) { // mask compression mode used for t2
			if (t2[1] == 0L) {
				for (int k = 2; k < t2.length; k += 2)
					if (t2[k] == i)
						return (t1[i] & t2[k + 1]) == 0L;
					else if (t2[k] > i)
						break;
			} else {
				for (int k = t2.length - 2; k >= 2; k -= 2)
					if (t2[k] == i) {
						return (t1[i] & t2[k + 1]) == 0L;
					} else if (t2[k] < i)
						break;
			}
			return (t1[i] & t2[0]) == 0L;
		}
		return (t1[i] & t2[i]) == 0L;
	}

	/**
	 * Returns the first index in the specified bit vectors where the intersection of the corresponding words is not 0,
	 * or -1 if no such position exists. Only positions in the specified dense set are considered. Possibly, mask
	 * compression may have been used for t2.
	 * 
	 * @param t1
	 *            a first bit vector defined by the sequence of bits over an array of long
	 * @param t2
	 *            a second bit vector defined by the sequence of bits over an array of long
	 * @param set
	 *            a dense set with positions of words (long) that are relevant for the bit vectors
	 * @return the first index in the specified bit vectors where the intersection of the corresponding words is not 0,
	 *         or -1 if no such position exists
	 */
	public static int firstNonNullIntersectionIndex(long[] t1, long[] t2, SetDense set) {
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

	/**
	 * Applies a bitwise 'or' on the two specified bit vectors, with the result being stored in the first one. Only
	 * indexes of words (longs) in the specified dense set are considered. Possibly, mask compression may have been used
	 * for the second bit vector.
	 * 
	 * @param inout
	 *            a first bit vector defined by the sequence of bits over an array of long
	 * @param in
	 *            a second bit vector defined by the sequence of bits over an array of long
	 * @param set
	 *            a dense set with the indexes of words (long) that are relevant for the bit vectors
	 */
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

	/**
	 * Applies a bitwise 'or' on the two specified bit vectors, after applying a bitwise "not" on the second bit vector,
	 * with the result being stored in the first one. Only indexes of words (longs) in the specified dense set are
	 * considered. Possibly, mask compression may have been used for the second bit vector.
	 * 
	 * @param inout
	 *            a first bit vector defined by the sequence of bits over an array of long
	 * @param in
	 *            a second bit vector defined by the sequence of bits over an array of long
	 * @param set
	 *            a dense set with the indexes of words (long) that are relevant for the bit vectors
	 */
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

	/**
	 * Inverses all bits of the specified bit vector, when only considering the words at indexes given by the specified
	 * dense set.
	 * 
	 * @param inout
	 *            a bit vector defined by the sequence of bits over an array of long
	 * @param set
	 *            a dense set with the indexes of words (long) that are relevant for the bit vector
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

	/**
	 * @param t
	 *            a bit vector defined by the sequence of bits over an array of longs
	 * @return the position in the specified bit vector of the first bit at 0
	 */
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
		System.out.println(firstNonInclusionIndex(t1, t2));
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
