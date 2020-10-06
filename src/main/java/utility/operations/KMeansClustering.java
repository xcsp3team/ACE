/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.operations;

import java.util.Arrays;

public abstract class KMeansClustering {

	private int[] values;

	public abstract int nValues();

	public abstract int value(int i);

	private double computeVariance(int from, int to, long sum) {
		double mean = sum / (double) (to - from + 1);
		double variance = 0;
		for (int i = from; i <= to; i++)
			variance += (values[i] - mean) * (values[i] - mean);
		return variance;
	}

	public KMeansClustering() {
		this.values = new int[nValues()];
	}

	public int recluster() {
		for (int i = 0; i < values.length; i++)
			values[i] = value(i);
		Arrays.sort(values);
		int frontier = 1;
		long leftSum = values[0], rightSum = 0;
		for (int i = frontier; i < values.length; i++)
			rightSum += values[i];
		double current = computeVariance(0, frontier - 1, leftSum) + computeVariance(frontier, values.length - 1, rightSum);
		double min = current;
		do {
			min = current;
			frontier++;
			leftSum += values[frontier];
			rightSum -= values[frontier];
			current = computeVariance(0, frontier - 1, leftSum) + computeVariance(frontier, values.length - 1, rightSum);
		} while (current < min && frontier < values.length - 1);
		return values[frontier - 1];
	}
}
