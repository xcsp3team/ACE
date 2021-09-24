/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import java.util.stream.IntStream;

import utility.Bit;

public final class Ips {

	/**
	 * nums[i] is the num(ber) of the ith variable involved in the IPS
	 */
	public final int[] nums;

	/**
	 * binDoms[i] is the binary representation of the domain of the ith variable involved in the IPS
	 */
	public final long[][] binDoms;

	/**
	 * The first watched position in nums; nums[watchPos0] is the number of the first watched involved variable
	 */
	private int watchPos0 = -1;

	/**
	 * The second watched position in nums; nums[watchPos1] is the number of the second watched involved variable
	 */
	private int watchPos1 = -1;

	/**
	 * The value index for the first watched position in nums
	 */
	private int watchIdx0 = -1;

	/**
	 * The value index for the second watched position in nums
	 */
	private int watchIdx1 = -1;

	public int varNumFor(int watch) {
		return nums[watch == 0 ? watchPos0 : watchPos1];
	}

	public int watchPosFor(int watch) {
		return watch == 0 ? watchPos0 : watchPos1;
	}

	public int watchIdxFor(int watch) {
		return watch == 0 ? watchIdx0 : watchIdx1;
	}

	public boolean isWatched(int x) {
		return nums[watchPos0] == x || nums[watchPos1] == x;
	}

	public int watchFor(int x) {
		// assert isWatched(x);
		return nums[watchPos0] == x ? 0 : 1;
	}

	public void setIndex(int watchPosition, int a) {
		if (watchPosition == 0)
			watchIdx0 = a;
		else
			watchIdx1 = a;
	}

	public void setWatch(int watch, int pos, int a) {
		if (watch == 0) {
			watchPos0 = pos;
			watchIdx0 = a;
		} else {
			watchPos1 = pos;
			watchIdx1 = a;
		}
	}

	public Ips(IpsRecorderDominance recorder, int[] nums) {
		this.nums = nums;
		this.binDoms = IntStream.of(nums).mapToObj(x -> recorder.solver.problem.variables[x].dom.binary().clone()).toArray(long[][]::new);
		recorder.nGeneratedIps++;
	}

	public Ips(IpsRecorderDominance recorder, boolean[] proof) {
		this(recorder, IntStream.range(0, proof.length).filter(i -> proof[i]).toArray());
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Ips))
			return false;
		Ips ips = (Ips) o;
		if (nums.length != ips.nums.length)
			return false;
		for (int i = 0; i < nums.length; i++)
			if (nums[i] != ips.nums[i])
				return false;
		for (int i = 0; i < binDoms.length; i++)
			for (int j = 0; j < binDoms[i].length; j++)
				if (binDoms[i][j] != ips.binDoms[i][j])
					return false;
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("IPS of size " + nums.length + " with watch1 = " + watchPos0 + " and watch2 = " + watchPos1 + "\n");
		for (int i = 0; i < nums.length; i++)
			sb.append(nums[i] + " : " + Bit.decrypt(binDoms[i]) + " \n");
		return sb.append("end\n").toString();
	}
}
