/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static utility.Kit.control;

import constraints.ConstraintGlobal;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.DomainFinite.DomainFiniteSpecial;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * 
 * @author Christophe Lecoutre
 */
public final class WakeUp extends ConstraintGlobal implements TagAC, TagCallCompleteFiltering {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		return t[0] < nSlices - 1 || (t[0] == nSlices - 1) && (t[1] < (nSlices - 1) * sliceLength + nValuesLastSlice);
	}

	VariableInteger master;

	VariableInteger servant;

	int minValue, maxValue, sliceLength, nSlices, nValuesLastSlice;

	public WakeUp(Problem pb, VariableInteger master, VariableInteger servant) {
		super(pb, new Variable[] { master, servant });
		this.master = master;
		this.servant = servant;
		this.minValue = ((DomainFiniteSpecial) servant.dom).initMinValue;
		this.maxValue = ((DomainFiniteSpecial) servant.dom).initMaxValue;
		this.sliceLength = ((DomainFiniteSpecial) servant.dom).sliceLength;
		this.nSlices = master.dom.initSize();

		this.nValuesLastSlice = (maxValue - minValue + 1) % sliceLength;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		//master.dom.display(1);
		if (master.assigned()) {
			// System.out.println("ffffffffffff " + master.dom.lastRemovedLevel() + " " + problem.solver.depth());

			control((master.dom.indexesMatchValues()));
			int startValue = minValue + (master.dom.single() * sliceLength);
			((DomainFiniteSpecial) servant.dom).shift(startValue);

			// if (v == nSlices - 1 && nValuesLastSlice > 0)
			// servant.dom.removeValuesGE(startValue + nValuesLastSlice);
			// specialVariable.dom.display(1);
			problem.solver.propagation.queue.add(servant);
			return entail();
		}
		return true;
	}
}
