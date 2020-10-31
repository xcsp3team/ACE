/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.global;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Map;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;
import org.xcsp.modeler.definitions.ICtr.ICtrAllDifferent;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public final class DistinctVectors2 extends CtrGlobal implements TagUnsymmetric, TagFilteringPartialAtEachCall, ICtrAllDifferent {

	@Override
	public boolean checkValues(int[] t) {
		if (mm != null) {
			for (int i = 0; i < list1.length; i++)
				if (t[mm.post1[i]] != t[mm.post2[i]])
					return true;
			return false;
		}
		for (int i = 0; i < list1.length; i++)
			if (t[i] != t[i + list1.length])
				return true;
		return false;
	}

	private Variable[] list1, list2;

	/**
	 * Two sentinels for tracking the presence of different values.
	 */
	private int sentinel1 = -1, sentinel2 = -1;

	private ManagerMultiOccurrences mm;

	public DistinctVectors2(Problem pb, Variable[] list1, Variable[] list2) {
		super(pb, pb.distinct(pb.vars(list1, list2)));
		Kit.control(list1.length == list2.length);
		this.list1 = list1;
		this.list2 = list2;
		this.sentinel1 = findAnotherSentinel();
		this.sentinel2 = findAnotherSentinel();
		Kit.control(sentinel1 != -1 && sentinel2 != -1, () -> "these particular cases not implemented yet");
		this.mm = scp.length != list1.length + list2.length ? new ManagerMultiOccurrences() : null;

	}

	private class ManagerMultiOccurrences {
		int[] post1, post2;

		ManagerMultiOccurrences() {
			post1 = IntStream.range(0, list1.length).map(i -> Utilities.indexOf(list1[i], scp)).toArray();
			post2 = IntStream.range(0, list2.length).map(i -> Utilities.indexOf(list2[i], scp)).toArray();
		}
	}

	@Override
	public boolean isGuaranteedAC() {
		return mm == null;
	}

	private boolean isSentinel(int i) {
		return list1[i].dom.size() > 1 || list2[i].dom.size() > 1 || list1[i].dom.uniqueValue() != list2[i].dom.uniqueValue();
	}

	private boolean isPossibleInferenceFor(int sentinel) {
		return (list1[sentinel].dom.size() == 1 && list2[sentinel].dom.size() > 1) || (list1[sentinel].dom.size() > 1 && list2[sentinel].dom.size() == 1);
	}

	private void handlePossibleInferenceFor(int sentinel) {
		assert isPossibleInferenceFor(sentinel);
		// no wipe-out possible
		if (list1[sentinel].dom.size() == 1)
			list2[sentinel].dom.removeValueIfPresent(list1[sentinel].dom.uniqueValue());
		else
			list1[sentinel].dom.removeValueIfPresent(list2[sentinel].dom.uniqueValue());
	}

	private int findAnotherSentinel() {
		for (int i = 0; i < list1.length; i++)
			if (i != sentinel1 && i != sentinel2 && isSentinel(i))
				return i;
		return -1;
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (x == list1[sentinel1] || x == list2[sentinel1]) {
			if (!isSentinel(sentinel1)) {
				int sentinel = findAnotherSentinel();
				if (sentinel != -1)
					sentinel1 = sentinel;
				else {
					if (list1[sentinel2].dom.size() > 1 && list2[sentinel2].dom.size() > 1)
						return true;
					else if (list1[sentinel2].dom.size() == 1 && list2[sentinel2].dom.size() == 1)
						return list1[sentinel2].dom.uniqueValue() != list2[sentinel2].dom.uniqueValue();
					else
						handlePossibleInferenceFor(sentinel2);
				}
			} else if (!isSentinel(sentinel2) && isPossibleInferenceFor(sentinel1))
				handlePossibleInferenceFor(sentinel1);
			return true;
		} else if (x == list1[sentinel2] || x == list2[sentinel2]) {
			if (!isSentinel(sentinel2)) {
				int sentinel = findAnotherSentinel();
				if (sentinel != -1)
					sentinel2 = sentinel;
				else {
					if (list1[sentinel1].dom.size() > 1 && list2[sentinel1].dom.size() > 1)
						return true;
					else if (list1[sentinel1].dom.size() == 1 && list2[sentinel1].dom.size() == 1)
						return list1[sentinel1].dom.uniqueValue() != list2[sentinel1].dom.uniqueValue();
					else
						handlePossibleInferenceFor(sentinel1);
				}
			} else if (!isSentinel(sentinel1) && isPossibleInferenceFor(sentinel2))
				handlePossibleInferenceFor(sentinel2);
			return true;
		} else
			return true;
	}

	@Override
	public Map<String, Object> mapXCSP() {
		return map(SCOPE, scp, LISTS, new String[] { compactOrdered(list1), compactOrdered(list2) });
	}

}
