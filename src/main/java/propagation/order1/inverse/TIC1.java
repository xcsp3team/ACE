/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.inverse;

import java.util.stream.Stream;

import org.xcsp.common.enumerations.EnumerationCartesian;

import constraints.Constraint;
import constraints.extension.CtrExtensionSTR1;
import constraints.extension.CtrExtensionSTR2;
import constraints.extension.structures.Table;
import search.Solver;
import utility.Enums.EStopping;
import utility.Kit;
import utility.sets.SetDenseReversible;
import variables.Variable;

public class TIC1 extends GIC1 {

	public TIC1(Solver solver) {
		super(solver);
		Kit.control(solver.rs.cp.settingExperimental.testI1 > 0
				|| Stream.of(solver.pb.constraints).allMatch(c -> c.getClass().isAssignableFrom(CtrExtensionSTR2.class)));
	}

	protected boolean isInverse(Variable[] scope, int[] tuple) {
		// Kit.prn("test " + Kit.implode(tuple));
		solver.resetNoSolutions();
		boolean consistent = true;
		Kit.control(solver.futVars.nDiscarded() == 0, () -> " BnbPast=" + solver.futVars.nDiscarded());
		int nVariablesAssignedBefore = solver.futVars.nDiscarded();
		for (int i = 0; consistent && i < scope.length; i++)
			if (scope[i].dom.isPresent(tuple[i])) {
				solver.assign(scope[i], tuple[i]);
				consistent = consistent && enforceArcConsistencyAfterAssignment(scope[i]);
			} else
				consistent = false;
		boolean inverse = consistent && solver.doRun().stoppingType == EStopping.REACHED_GOAL;
		for (int j = solver.futVars.nDiscarded() - nVariablesAssignedBefore - 1; j >= 0; j--)
			solver.backtrack(scope[j]);
		Kit.control(solver.futVars.nDiscarded() == 0, () -> " AnbPast=" + solver.futVars.nDiscarded());
		return inverse;
	}

	private int filterConstraint(Constraint ctr) {
		int cnt = 0;
		Kit.log.info("Filter tuples from " + ctr);
		int[][] tuples = ((Table) ctr.extStructure()).tuples;
		SetDenseReversible denseSetOfTuples = ((CtrExtensionSTR1) ctr).set;
		int[] dense = denseSetOfTuples.dense;
		for (int i = denseSetOfTuples.limit; i >= 0; i--) {
			denseSetOfTuples.swapAtPositions(0, i);
			int prevLimit = denseSetOfTuples.limit;
			denseSetOfTuples.limit = 0;
			boolean inverse = isInverse(ctr.scp, tuples[dense[0]]);
			denseSetOfTuples.swapAtPositions(0, i);
			denseSetOfTuples.limit = prevLimit; // limit restored
			if (!inverse) {
				cnt++;
				denseSetOfTuples.removeAtPosition(i, solver.depth());
			}
		}
		if (cnt > 0)
			Kit.log.info(cnt + " tuples removed from " + ctr);
		Kit.control(denseSetOfTuples.size() > 0, () -> "Impossible because the CN is GIC");
		return cnt;
	}

	@Override
	public boolean enforceStrongConsistency() {
		if (solver.rs.cp.settingExperimental.testI1 > 0) {
			performingProperSearch = true;
			Variable[] vars = new Variable[solver.rs.cp.settingExperimental.testI1];
			int[] t = Kit.range(solver.pb.variables.length);
			for (int i = 0; i < vars.length; i++) {
				int id = solver.rs.random.nextInt(t.length - i);
				vars[i] = solver.pb.variables[id];
				t[id] = t[t.length - 1 - i];
			}
			Kit.control(Variable.areAllDistinct(vars));

			EnumerationCartesian ec = new EnumerationCartesian(Variable.domSizeArrayOf(vars, true));
			// ec.displayAllTuples();
			ec.reset();
			int cnt = 0;
			while (ec.hasNext())
				if (!isInverse(vars, ec.next()))
					cnt++;
			Kit.log.info(cnt + " tuples removed from " + Kit.join(vars));
			performingProperSearch = false;
			cp().settingSolving.enableSearch = false;
			return true;
		} else {
			boolean consistent = super.enforceStrongConsistency();
			Kit.control(consistent);
			if (solver.depth() > 0)
				return true;
			performingProperSearch = true;
			int nbTuplesRemoved = 0;
			for (Constraint ctr : solver.pb.constraints)
				nbTuplesRemoved += filterConstraint(ctr);
			if (verbose >= 1 && nbTuplesRemoved > 0)
				Kit.log.info("nbTICInconsistentTuples=" + nbTuplesRemoved + " at depth=" + solver.depth() + "\n");
			solver.resetNoSolutions();
			performingProperSearch = false;
			return true;
		}
	}
}
