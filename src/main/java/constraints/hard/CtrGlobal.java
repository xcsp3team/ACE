/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard;

import constraints.Constraint;
import interfaces.FilteringGlobal;
import problem.Problem;
import variables.Variable;

public abstract class CtrGlobal extends Constraint implements FilteringGlobal {

	protected final void defineKey(Object... specificData) {
		StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
		for (Object data : specificData)
			sb.append(' ').append(data.toString());
		this.key = sb.toString(); // getSignature().append(' ').append(this.getClass().getSimpleName()).append(' ') + o.toString();
	}

	public CtrGlobal(Problem pb, Variable[] scp) {
		super(pb, scp);
		filteringComplexity = 1;
	}
}
