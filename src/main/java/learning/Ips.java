/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import java.util.stream.IntStream;

import utility.Bit;
import utility.Kit;
import variables.Variable;

public final class Ips {

	public static boolean FIRST_WATCH = true;
	public static boolean SECOND_WATCH = false;

	public final int[] nums; // nums[i] is the num(ber) of the ith involved variable

	public final long[][] binDoms; // binDoms[i] is the binary representation of the domain of the ith involved variable

	private int watchVar0 = -1;

	private int watchVar1 = -1;

	private int watchIdx0 = -1;

	private int watchIdx1 = -1;

	public int varNumFor(int watch) {
		return nums[watch == 0 ? watchVar0 : watchVar1];
	}

	public long[] binDomFor(int watch) {
		return binDoms[watch == 0 ? watchVar0 : watchVar1];
	}

	public int watchVarFor(int watch) {
		return watch == 0 ? watchVar0 : watchVar1;
	}

	public int watchIdxFor(int watch) {
		return watch == 0 ? watchIdx0 : watchIdx1;
	}

	public boolean isWatched(int x) {
		return nums[watchVar0] == x || nums[watchVar1] == x;
	}

	public int watchFor(int x) {
		// assert isWatched(x);
		return nums[watchVar0] == x ? 0 : 1;
	}

	public void setIndex(int watchPosition, int a) {
		if (watchPosition == 0)
			watchIdx0 = a;
		else
			watchIdx1 = a;
	}

	public void setWatch(int watch, int pos, int a) {
		if (watch == 0) {
			watchVar0 = pos;
			watchIdx0 = a;
		} else {
			watchVar1 = pos;
			watchIdx1 = a;
		}
	}

	public Ips(IpsRecorderForDominance recorder, int[] nums) {
		this.nums = nums;
		Variable[] variables = recorder.solver.problem.variables;
		this.binDoms = IntStream.of(nums).mapToObj(x -> variables[x].dom.binary().clone()).toArray(long[][]::new);
		recorder.nGeneratedIps++;
	}

	public Ips(IpsRecorderForDominance recorder, Ips ips, boolean[] proof) {
		int cnt = Kit.countIn(true, proof);
		this.nums = new int[cnt];
		this.binDoms = new long[cnt][];
		for (int i = 0, j = 0; i < proof.length; i++) {
			if (proof[i]) {
				nums[j] = i;
				binDoms[j] = recorder.solver.problem.variables[i].dom.binary().clone();
				// binDoms[cnt] = solver != null ? solver.problem.variables[i].dom.binary().clone() :ips.binDoms[i];
				j++;
			}
		}
		recorder.nGeneratedIps++;
	}

	public boolean equals(Object o) {
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

	public String toString() {
		StringBuilder sb = new StringBuilder().append("IPS of size " + nums.length + " with watch1 = " + watchVar0 + " and watch2 = " + watchVar1 + "\n");
		for (int i = 0; i < nums.length; i++)
			sb.append(nums[i] + " : " + Bit.decrypt(binDoms[i]) + " \n");
		return sb.append("end\n").toString();
	}
}
