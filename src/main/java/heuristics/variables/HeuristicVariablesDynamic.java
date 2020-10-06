/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.variables;

import interfaces.TagMaximize;
import search.backtrack.SolverBacktrack;
import utility.Enums.EBranching;
import utility.Enums.ESingletonAssignment;
import utility.operations.CombinatorOfTwoInts;
import variables.Variable;

/**
 * This class gives the description of a dynamic variable ordering heuristic. <br>
 * It means that at each step of the search, this kind of object is solicited in order to determine which variable has to be selected according to the
 * current state of the problem.
 */
public abstract class HeuristicVariablesDynamic extends HeuristicVariables {

	public HeuristicVariablesDynamic(SolverBacktrack solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	private int lastDepthWithOnlySingletons = Integer.MAX_VALUE;

	@Override
	protected final Variable bestUnpriorityVar() {
		assert solver.futVars.size() > 0;

		if (solver.rs.cp.solving.branching != EBranching.BIN) {
			Variable x = solver.dr.varOfLastDecisionIf(false);
			if (x != null)
				return x;
		}
		if (settings.lastConflictSize > 0) {
			Variable x = solver.lcReasoner.lastConflictPriorityVar();
			if (x != null) {
				return x;
			}
		}
		bestScoredVariable.reset(false);
		if (settings.singletonAssignment == ESingletonAssignment.LAST) {
			if (solver.depth() <= lastDepthWithOnlySingletons) {
				lastDepthWithOnlySingletons = Integer.MAX_VALUE;
				solver.futVars.execute(x -> {
					if (x.dom.size() != 1)
						bestScoredVariable.update(x, scoreOptimizedOf(x));
				});
			}
			if (bestScoredVariable.variable == null) {
				lastDepthWithOnlySingletons = solver.depth();
				return solver.futVars.first();
			}
		} else {
			boolean first = settings.singletonAssignment == ESingletonAssignment.FIRST;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (first && x.dom.size() == 1)
					return x;
				bestScoredVariable.update(x, scoreOptimizedOf(x));
			}
		}
		return bestScoredVariable.variable;

	}

	// ************************************************************************
	// ***** Subclasses
	// ************************************************************************

	public static final class DDeg extends HeuristicVariablesDynamic implements TagMaximize {

		public DDeg(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddeg();
		}
	}

	public static final class DDegOnDom extends HeuristicVariablesDynamic implements TagMaximize {

		public DDegOnDom(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddegOnDom();
		}
	}

	public static final class Dom extends HeuristicVariablesDynamic {

		public Dom(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.dom.size();
		}
	}

	public static final class DomThenDeg extends HeuristicVariablesDynamic {
		private CombinatorOfTwoInts combinator;

		public DomThenDeg(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.combinator = new CombinatorOfTwoInts(solver.pb.stuff.maxVarDegree());
		}

		@Override
		public double scoreOf(Variable x) {
			return combinator.combinedMaxMinLongValueFor(x.dom.size(), x.deg());
		}
	}

}
