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
import propagation.order1.StrongConsistency;
import search.Solver;
import sets.SetDenseReversible;
import utility.Enums.EStopping;
import utility.Kit;
import variables.Variable;

public class TIInverse1 extends StrongConsistency {

	private int rate = 10;

	private Constraint selectedConstraint;

	private Constraint[] ignoredConstraints;

	private int[][] residues;

	private void selectConstraints() {
		Constraint[] ctrs = solver.pb.constraints;
		// selectedConstraint = constraints[solver.resolution.random.nextInt(constraints.length)];
		selectedConstraint = ctrs[11]; // 10 et 11 pour big 70 pour megane 139 pour master
										// solver.resolution.random.nextInt(constraints.length)];
		ignoredConstraints = new Constraint[Math.round((ctrs.length * rate) / 100)];
		for (int i = 0; i < ignoredConstraints.length; i++) {
			while (true) {
				int id = solver.rs.random.nextInt(ctrs.length);
				if (id == selectedConstraint.num)
					continue;
				boolean alreadyIgnored = false;
				for (int j = 0; !alreadyIgnored && j < i; j++)
					if (id == ignoredConstraints[j].num)
						alreadyIgnored = true;
				if (!alreadyIgnored) {
					ignoredConstraints[i] = ctrs[id];
					ignoredConstraints[i].ignored = true;
					break;
				}
			}
		}
		int nTuples = ((Table) selectedConstraint.extStructure()).tuples.length;
		Kit.log.info(selectedConstraint + " nbTuples=" + nTuples);
		Kit.log.info(Kit.join(ignoredConstraints));
		residues = new int[nTuples][]; // solver.problem.variables.length];
	}

	public TIInverse1(Solver solver) {
		super(solver);
		Kit.control(Stream.of(solver.pb.constraints).allMatch(c -> c.getClass().isAssignableFrom(ExtensionSTR2.class)));
		selectConstraints();

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
		for (int j = solver.futVars.nDiscarded() - nVariablesAssignedBefore - 1; j >= 0; j--)
			solver.backtrack(scope[j]);
		Kit.control(solver.futVars.nDiscarded() == 0, () -> " AnbPast=" + solver.futVars.nDiscarded());
		return inverse;
	}

	private int filterConstraint(Constraint ctr) {
		int cnt = 0;
		int[][] tuples = ((Table) ctr.extStructure()).tuples;
		SetDenseReversible denseSetOfTuples = ((ExtensionSTR1) ctr).set;
		int[] dense = denseSetOfTuples.dense;
		for (int i = denseSetOfTuples.limit; i >= 0; i--) {
			if (residues[dense[i]] != null && Constraint.firstUnsatisfiedHardConstraint(solver.pb.constraints, residues[dense[i]]) != null)
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
			} else {
				int[] solution = solver.solManager.lastSolution;
				if (residues[dense[i]] == null)
					residues[dense[i]] = new int[solver.pb.variables.length];
				Kit.copy(solution, residues[dense[i]]);
			}
		}
		if (cnt > 0)
			Kit.log.info(cnt + " tuples removed from " + ctr);
		Kit.control(denseSetOfTuples.size() > 0, () -> "Impossible because the CN is GIC");
		return cnt;
	}

	@Override
	public boolean enforceStrongConsistency() {
		if (solver.depth() > 0)
			return true;
		performingProperSearch = true;
		Kit.log.info("Filter tuples from " + selectedConstraint + " nbTuples=" + ((Table) selectedConstraint.extStructure()).tuples.length);
		filterConstraint(selectedConstraint);
		for (int i = 0; i < ignoredConstraints.length; i++) {
			ignoredConstraints[i].ignored = false;
			filterConstraint(selectedConstraint);
		}
		solver.resetNoSolutions();
		performingProperSearch = false;
		return true;
	}
}
