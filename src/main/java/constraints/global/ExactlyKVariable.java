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
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * Exactly k variables of the specified vector of variables, where k is a variable, must be assigned to the specified value
 * 
 */
public final class ExactlyKVariable extends CtrGlobal implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	@Override
	public boolean checkValues(int[] t) {
		return indexOfKInList != -1 ? Count.countIn(value, t) == t[indexOfKInList] : Count.countIn(value, t, 0, t.length - 1) == t[t.length - 1];
	}

	protected Variable[] list;
	protected int value;
	protected Variable k;

	private int indexOfKInList; // -1 if not present

	@Override
	public int[] defineSymmetryMatching() {
		return IntStream.range(0, scp.length).map(i -> i == indexOfKInList || (indexOfKInList == -1 && i == scp.length - 1) ? 2 : 1).toArray();
		// int[] sym = Kit.repeat(1, scp.length);
		// sym[indexOfKInVector != -1 ? indexOfKInVector : list.length - 1] = 2;
		// return sym;
	}

	public ExactlyKVariable(Problem pb, Variable[] list, int value, Variable k) {
		super(pb, Utilities.collect(Variable.class, list, k)); // before, was collectDistinct (but put in the constructor of Constraint)
		this.list = list;
		this.value = value;
		this.k = k;
		this.indexOfKInList = Utilities.indexOf(k, list);
		defineKey(value, indexOfKInList);
		// TODO : controls to be added
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		// System.out.println("Run " + this);
		// counting the nb of occurrences of value in list
		int nGuaranteedOccurrences = 0, nPossibleOccurrences = 0;
		for (Variable x : list)
			if (x.dom.isPresentValue(value)) {
				nPossibleOccurrences++;
				if (x.dom.size() == 1)
					nGuaranteedOccurrences++;
			}
		Domain domK = k.dom;
		if (domK.size() == 1) {
			int valK = domK.uniqueValue();
			if (valK < nGuaranteedOccurrences || nPossibleOccurrences < valK)
				return domK.fail();
		} else {
			// possible update of the domain of k when present in the vector, first by removing value (if present)
			// so as to update immediately nPossibleOccurrences
			if (indexOfKInList != -1) {
				int a = domK.toPresentIdx(value);
				if (a != -1) {
					boolean deleted = false;
					for (int b = domK.first(); b != -1; b = domK.next(b))
						if (b == a) {
							if (value < nGuaranteedOccurrences + 1 || nPossibleOccurrences < value) { // +1 by assuming we assign the value
								if (domK.remove(a) == false)
									return false;
								deleted = true;
							}
						} else {
							int v = domK.toVal(b);
							if (v < nGuaranteedOccurrences || nPossibleOccurrences - 1 < v) { // -1 by assuming we assign v (and not val)
								if (domK.remove(b) == false)
									return false;
							}
						}
					if (deleted)
						nPossibleOccurrences--;
				} else {
					if (domK.removeValuesLT(nGuaranteedOccurrences) == false || domK.removeValuesGT(nPossibleOccurrences) == false)
						return false;
				}
			} else if (domK.removeValuesLT(nGuaranteedOccurrences) == false || domK.removeValuesGT(nPossibleOccurrences) == false)
				return false;
		}
		// if k is singleton, updating the domain of the other variables
		if (domK.size() == 1) {
			int v = domK.uniqueValue();
			if (v == nGuaranteedOccurrences)
				for (Variable x : list)
					if (x.dom.size() > 1 && x.dom.isPresentValue(value))
						if (!x.dom.removeValue(value))
							return false;
			if (v == nPossibleOccurrences)
				for (Variable x : list)
					if (x.dom.size() > 1 && x.dom.isPresentValue(value))
						x.dom.reduceToValue(value);
		}
		return true;
	}
}
