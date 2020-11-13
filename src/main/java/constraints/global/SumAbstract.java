/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import constraints.Constraint.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class SumAbstract extends CtrGlobal implements TagFilteringCompleteAtEachCall {

	protected long limit;

	protected long min;
	protected long max; // used in most of the subclasses

	public final long getLimit() {
		return limit;
	}

	public final void setLimit(long newLimit) {
		this.limit = newLimit;
	}

	public SumAbstract(Problem pb, Variable[] scp, long limit) {
		super(pb, scp);
		this.limit = limit;
		control(scp.length > 1);
	}

	/**
	 * Only used in some subclasses
	 */
	protected boolean controlFCLevel() {
		int singletonPosition = -1;
		for (int i = 0; i < scp.length; i++) {
			if (scp[i].dom.size() == 1)
				vals[i] = scp[i].dom.uniqueValue();
			else if (singletonPosition == -1)
				singletonPosition = i;
			else
				return true;
		}
		if (singletonPosition == -1)
			return checkValues(vals);
		Variable x = scp[singletonPosition];
		for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
			vals[singletonPosition] = x.dom.toVal(a);
			Kit.control(checkValues(vals), () -> "pb with " + Kit.join(vals));
		}
		return true;
	}
}
