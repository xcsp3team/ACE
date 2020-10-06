/**
 *  AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 *  All rights reserved. 
 *  
 *  This program and the accompanying materials are made 
 *  available under the terms of the CONTRAT DE LICENCE 
 *  DE LOGICIEL LIBRE CeCILL which accompanies this distribution, 
 *  and is available at http://www.cecill.info
 */
package propagation.order2.dual;

import constraints.Constraint;
import constraints.hard.CtrExtension;
import search.Solver;
import variables.Variable;

public final class CDC1 extends DualBasedConsistency {

	public CDC1(Solver solver) {
		super(solver);
	}

	@Override
	protected int removeTuplesAfterSingletonTestOn(Variable x, int a) {
		int nbTuplesBefore = pb().nTuplesRemoved;
		for (Constraint c : x.ctrs)
			if (c.scp.length == 2 && c instanceof CtrExtension)
				removeTuplesFrom(x, a, c);
		return pb().nTuplesRemoved - nbTuplesBefore;
	}

}