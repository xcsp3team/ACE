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

import constraints.Constraint;
import constraints.extension.ExtensionSTR1;
import constraints.extension.ExtensionSTR2;
import constraints.extension.structures.Table;
import search.Solver;
import sets.SetDenseReversible;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public class TIC4 extends GIC4 {

	private int[][] tsolutions;

	protected int currentLimitOfTSolutions;

	protected void checkTSolutions() {
		Variable[] variables = solver.pb.variables;
		for (int i = currentLimitOfTSolutions; i >= 0; i--) {
			int[] solution = tsolutions[i];
			boolean valid = true;
			for (int j = variables.length - 1; j >= 0; j--) {
				if (!variables[j].dom.isPresent(solution[j])) {
					valid = false;
					break;
				}
			}
			if (!valid)
				Kit.swap(tsolutions, i, currentLimitOfTSolutions--);
			// solution removed but we swap to save the array (in order to avoid building a new array object
		}
	}

	int[][] increaseArray(int[][] m) {
		int[][] tmp = new int[m.length * 2][];
		for (int i = 0; i < m.length; i++)
			tmp[i] = m[i];
		return tmp;
	}

	protected void handleNewTSolution() {
		currentLimitOfTSolutions++;
		if (currentLimitOfTSolutions >= tsolutions.length)
			tsolutions = increaseArray(tsolutions);
		if (tsolutions[currentLimitOfTSolutions] == null)
			tsolutions[currentLimitOfTSolutions] = new int[solver.pb.variables.length];
		int[] solution = solver.solManager.lastSolution;
		Kit.copy(solution, tsolutions[currentLimitOfTSolutions]);
	}

	protected boolean isSupported(Variable[] scope, int[] tuple) {
		for (int i = currentLimitOfTSolutions; i >= 0; i--) {
			int[] solution = tsolutions[i];
			boolean supported = true;
			for (int j = scope.length - 1; j >= 0; j--) {
				int id = scope[j].num;
				if (solution[id] != tuple[j]) {
					supported = false;
					break;
				}
			}
			if (supported)
				return true;
		}
		return false;
	}

	public TIC4(Solver solver) {
		super(solver);
		Kit.control(Stream.of(solver.pb.constraints).allMatch(c -> c.getClass().isAssignableFrom(ExtensionSTR2.class)));
		Kit.control(Variable.areNumsNormalized(solver.pb.variables));
		tsolutions = new int[solver.pb.constraints.length * 100][];
		currentLimitOfTSolutions = -1;
	}

	protected boolean isInverse(Variable[] scope, int[] tuple) {
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
		if (inverse)
			handleNewTSolution();

		for (int j = solver.futVars.nDiscarded() - nVariablesAssignedBefore - 1; j >= 0; j--)
			solver.backtrack(scope[j]);
		Kit.control(solver.futVars.nDiscarded() == 0, () -> " AnbPast=" + solver.futVars.nDiscarded());
		return inverse;
	}

	private int filterConstraint(Constraint ctr) {
		int cnt = 0;
		Kit.log.info("Filter tuples from " + ctr);
		int[][] tuples = ((Table) ctr.extStructure()).tuples;
		SetDenseReversible denseSetOfTuples = ((ExtensionSTR1) ctr).set;
		int[] dense = denseSetOfTuples.dense;
		for (int i = denseSetOfTuples.limit; i >= 0; i--) {
			if (isSupported(ctr.scp, tuples[dense[i]]))
				continue;
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
		boolean consistent = super.enforceStrongConsistency();
		Kit.control(consistent);
		if (solver.depth() > 0)
			return true;

		performingProperSearch = true;
		int nTuplesRemoved = 0;
		for (Constraint ctr : solver.pb.constraints)
			nTuplesRemoved += filterConstraint(ctr);
		if (verbose >= 1 && nTuplesRemoved > 0)
			Kit.log.info("nbTICInconsistentTuples=" + nTuplesRemoved + " at depth=" + solver.depth() + "\n");
		solver.resetNoSolutions();
		performingProperSearch = false;
		return true;
	}
}
