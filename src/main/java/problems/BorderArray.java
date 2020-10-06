/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems;

import java.util.Arrays;

import utility.Kit;

public class BorderArray {
	private char[][] m;

	private int cellWidth, cellHeight;

	public BorderArray(int nRows, int nColumns, int cellWidth, int cellHeight, char initialValue) {
		this.cellWidth = cellWidth;
		this.cellHeight = cellHeight;
		this.m = new char[(1 + cellHeight) * nRows + 1][(1 + cellWidth) * nColumns + 1];
		for (char[] t : m)
			Arrays.fill(t, initialValue);
	}

	public BorderArray(int nRows, int nColumns, int cellWidth, int cellHeight) {
		this(nRows, nColumns, cellWidth, cellHeight, ' ');
	}

	public BorderArray(int nRows, int nColumns) {
		this(nRows, nColumns, 2, 1);
	}

	public void writeBorder(int left, int right, int top, int bottom) {
		for (int j = left; j < right; j++) {
			for (int k = 1; k <= cellWidth; k++) {
				m[(1 + cellHeight) * top][(1 + cellWidth) * j + k] = '-';
				m[(1 + cellHeight) * bottom][(1 + cellWidth) * j + k] = '-';
			}
		}
		for (int j = top; j < bottom; j++) {
			for (int k = 1; k <= cellHeight; k++) {
				m[(1 + cellHeight) * j + k][(1 + cellWidth) * left] = '|';
				m[(1 + cellHeight) * j + k][(1 + cellWidth) * right] = '|';
			}
		}
	}

	public void writeBorder(String left, String right, String top, String bottom) {
		writeBorder(Integer.parseInt(left), Integer.parseInt(right), Integer.parseInt(top), Integer.parseInt(bottom));
	}

	public void writeValue(int i, int j, int value) {
		Kit.control(value >= 0 && value < Math.pow(10, cellWidth));
		int k = cellWidth;
		do {
			m[(1 + cellHeight) * i + 1][(1 + cellWidth) * j + k] = (char) ('0' + value % 10);
			value = value / 10;
			k--;
		} while (value > 0);
	}

	@Override
	public String toString() {
		return Kit.join(m, "\n", "");
	}
}
