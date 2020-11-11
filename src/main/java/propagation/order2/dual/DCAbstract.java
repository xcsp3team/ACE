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
import constraints.extension.CtrExtension;
import search.Solver;
import search.backtrack.DecisionRecorder;
import search.backtrack.SolverBacktrack;
import utility.sets.SetSparse;
import variables.Variable;

public abstract class DCAbstract extends DualBasedConsistency {

	private SetSparse sparseSet;

	protected final DecisionRecorder dr;

	public DCAbstract(Solver solver) {
		super(solver);
		sparseSet = new SetSparse(solver.pb.variables.length, true);
		dr = ((SolverBacktrack) solver).dr;
	}

	protected abstract boolean removeAdditionalTuples(Variable x, int a, Variable y);

	@Override
	protected int removeTuplesAfterSingletonTestOn(Variable x, int a) {
		int nbTuplesBefore = nTuplesRemoved;
		sparseSet.fill();
		sparseSet.remove(x.num);
		for (Constraint c : x.ctrs)
			if (c.scp.length == 2 && c instanceof CtrExtension) {
				removeTuplesFrom(x, a, c);
				sparseSet.remove(Variable.firstDifferentVariableIn(c.scp, x).num);
			}
		Variable[] variables = solver.pb.variables;
		for (int i = 0; i <= sparseSet.limit; i++)
			removeAdditionalTuples(x, a, variables[sparseSet.dense[i]]);
		return nTuplesRemoved - nbTuplesBefore;
	}
}
