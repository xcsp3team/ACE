/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility.operations;

import java.util.stream.IntStream;

import utility.Kit;

/**
 * This class allows to perform some translations from base 10 to a given base.
 */
public class Base {

	/**
	 * Returns the decimal value (value in base 10) that corresponds to the given number expressed in the given base. The given number is an array
	 * which contains digits in the given base.
	 * 
	 * @param number
	 *            the given number
	 * @param base
	 *            the given base
	 * @return the decimal value that corresponds to the given number in the given base
	 */
	public static long decimalValueFor(int[] number, int base) {
		assert IntStream.of(number).noneMatch(v -> v >= base);
		double decimalValue = number[0];
		for (int i = 1; i < number.length; i++)
			decimalValue = decimalValue * base + number[i];
		assert decimalValue <= Long.MAX_VALUE : "The decimal value = " + decimalValue + "is too big to be represented by a long integer";
		return (long) decimalValue;
	}

	/**
	 * Returns the decimal value (value in base 10) that corresponds to the given number expressed using the given bases. The given number is an array
	 * which contains digits in the corresponding given bases.
	 * 
	 * @param number
	 *            the given number
	 * @param bases
	 *            the given bases
	 * @return the decimal value that corresponds to the given number expressed using the given base
	 */
	public static long decimalValueFor(int[] number, int[] bases) {
		assert number.length == bases.length && IntStream.range(0, number.length).noneMatch(i -> number[i] >= bases[i]);
		double decimalValue = number[0];
		for (int i = 1; i < number.length; i++)
			decimalValue = decimalValue * bases[i] + number[i];
		assert decimalValue <= Long.MAX_VALUE : "The decimal value = " + decimalValue + "is too big to be represented by a long integer";
		return (long) decimalValue;
	}

	/**
	 * Returns the value in the specified base that corresponds to the specified decimal value (value in base 10). The returned value is an array of
	 * the specified length that contains digits in the given base.
	 * 
	 * @param decimalValue
	 *            a decimal value
	 * @param length
	 *            the number of digits composing the result
	 * @param base
	 *            a base (e.g., 2, 8 or 16)
	 * @return the value in the specified base that corresponds to the specified decimal value
	 */
	public static int[] baseValueFor(long decimalValue, int length, int base) {
		int[] value = new int[length];
		for (int i = value.length - 1; i >= 0; i--) {
			value[i] = (int) (decimalValue % base);
			decimalValue = decimalValue / base;
		}
		assert decimalValue == 0 : "The given array is too small to contain all the digits of the conversion";
		return value;
	}

	/**
	 * Returns the value, expressed using the given bases, that corresponds to the given decimal value (value in base 10). This returned value
	 * corresponds to an array which contains digit, a digit for each base.
	 * 
	 * @param decimalValue
	 *            the given decimal value
	 * @param value
	 *            the array used to store all the digits of the number in the given base which corresponds to the given decimal value
	 * @param bases
	 *            the given bases
	 * @return the value expressed using the given bases
	 */
	public static int[] valueFor(long decimalValue, int[] value, int[] bases) {
		for (int i = value.length - 1; i >= 0; i--) {
			value[i] = (int) (decimalValue % bases[i]);
			decimalValue = decimalValue / bases[i];
		}
		Kit.control(decimalValue == 0, () -> "The given array is too small to contain all the digits of the conversion");
		return value;
	}

}
