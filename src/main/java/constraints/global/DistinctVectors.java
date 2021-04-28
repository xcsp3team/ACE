/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.Constraint.CtrGlobal;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

// 279360 solutions for:
// java ace Crossword-ogd-p02.xml.lzma -s=all -ev -varh=Dom -g_dv=1 -st  // smart tables
// java ace Crossword-ogd-p02.xml.lzma -s=all -ev -varh=Dom  // distinct vectors
// java ace Crossword-ogd-p02.xml.lzma -s=all -ev -di=0 -sl=42 -varh=Dom -g_dv=1  // intention
// When the same variable occurs several times, DistinctVectors does not guarantee full GAC

public final class DistinctVectors extends CtrGlobal implements ObserverBacktrackingSystematic, TagFilteringCompleteAtEachCall, TagNotSymmetric {

	@Override
	public void restoreBefore(int depth) {
		if (uniqueSentinelLevel == depth)
			uniqueSentinelLevel = -1;
	}

	@Override
	public boolean checkValues(int[] t) {
		for (int i = 0; i < half; i++)
			if (t[pos1[i]] != t[pos2[i]])
				return true;
		return false;
	}

	@Override
	public boolean isGuaranteedAC() {
		return scp.length == 2 * half; // if not several occurrences of the same variable
	}

	private Variable[] list1, list2;

	private int[] pos1, pos2;

	private int half;

	/**
	 * Initial mode: two sentinels for tracking the presence of different values.
	 */
	private int sentinel1 = -1, sentinel2 = -1;

	/**
	 * Possible mode: only one remaining sentinel, identified at a certain level
	 */
	private int uniqueSentinel, uniqueSentinelLevel = -1;

	public DistinctVectors(Problem pb, Variable[] list1, Variable[] list2) {
		super(pb, pb.vars(list1, list2));
		this.half = list1.length;
		this.list1 = list1;
		this.list2 = list2;
		control(half > 1 && half == list2.length && IntStream.range(0, half).allMatch(i -> list1[i] != list2[i]),
				" " + half + " " + Kit.join(list1) + " " + Kit.join(list2));
		this.pos1 = IntStream.range(0, half).map(i -> Utilities.indexOf(list1[i], scp)).toArray();
		this.pos2 = IntStream.range(0, half).map(i -> Utilities.indexOf(list2[i], scp)).toArray();
		this.sentinel1 = 0;
		this.sentinel2 = half - 1;
	}

	private boolean handleUniqueSentinel(Domain dom1, Domain dom2) {
		if (dom1.size() > 1 && dom2.size() > 1)
			return true;
		if (dom1.size() == 1)
			return dom2.removeValueIfPresent(dom1.uniqueValue()) && entailed();
		return dom1.removeValueIfPresent(dom2.uniqueValue()) && entailed();
	}

	private boolean isGoodSentinel(Domain dom1, Domain dom2) {
		return dom1.size() > 1 || dom2.size() > 1 || dom1.uniqueValue() != dom2.uniqueValue();
	}

	private int findAnotherSentinel() {
		for (int i = 0; i < half; i++)
			if (i != sentinel1 && i != sentinel2 && isGoodSentinel(list1[i].dom, list2[i].dom))
				return i;
		return -1;
	}

	@Override
	public boolean runPropagator(Variable event) {
		if (uniqueSentinelLevel != -1)
			return handleUniqueSentinel(list1[uniqueSentinel].dom, list2[uniqueSentinel].dom);

		Domain dx1 = list1[sentinel1].dom, dx2 = list2[sentinel1].dom, dy1 = list1[sentinel2].dom, dy2 = list2[sentinel2].dom;
		if (dx1.size() == 1 && dx2.size() == 1) { // possibly, sentinel1 is no more valid
			if (dx1.uniqueValue() != dx2.uniqueValue())
				return entailed();
			int sentinel = findAnotherSentinel();
			if (sentinel != -1) {
				sentinel1 = sentinel;
				dx1 = list1[sentinel1].dom;
				dx2 = list2[sentinel1].dom;
			} else {
				uniqueSentinel = sentinel2;
				uniqueSentinelLevel = problem.solver.depth();
				return handleUniqueSentinel(dy1, dy2);
			}
		}
		if (dy1.size() == 1 && dy2.size() == 1) { // possibly, sentinel2 is no more valid
			if (dy1.uniqueValue() != dy2.uniqueValue())
				return entailed();
			int sentinel = findAnotherSentinel();
			if (sentinel != -1) {
				sentinel2 = sentinel;
			} else {
				uniqueSentinel = sentinel1;
				uniqueSentinelLevel = problem.solver.depth();
				return handleUniqueSentinel(dx1, dx2);
			}
		}
		return true;
	}
}
