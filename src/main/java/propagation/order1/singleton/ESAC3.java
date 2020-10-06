/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1.singleton;

import java.util.stream.IntStream;

import heuristics.variables.HeuristicVariables;
import heuristics.variables.HeuristicVariables.BestScoredVariable;
import heuristics.variables.dynamic.WDegOnDom;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;

public class ESAC3 extends SACGreedy {

	private Variable lastFailedVar;

	private int lastFailedIdx;

	private Variable currSelectedVar;

	private int currSelectedIdx;

	private int currIndexOfVarHeuristic = -1;

	private HeuristicVariables[] varHeuristics;

	private QueueESAC queueESAC;

	class QueueESAC {

		private int nUncheckedVars;

		private Variable[] uncheckedVars;

		private BestScoredVariable bestScoredVariable = new BestScoredVariable();

		private QueueESAC() {
			this.uncheckedVars = new Variable[solver.pb.variables.length];
		}

		public void initialize() {
			nUncheckedVars = 0;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
				if (shavingEvaluator == null || shavingEvaluator.isEligible(x))
					uncheckedVars[nUncheckedVars++] = x;
				else
					shavingEvaluator.updateRatioAfterUntest(x);
		}

		public Variable selectNextVariable() {
			bestScoredVariable.reset(false);
			if (nUncheckedVars == 0) { // we keep building the branch
				solver.futVars.execute(x -> bestScoredVariable.update(x, varHeuristics[currIndexOfVarHeuristic].scoreOptimizedOf(x)));
			} else {
				assert controlUncheckedVariables();
				int bestPos = 0;
				for (int i = 0; i < nUncheckedVars; i++)
					if (bestScoredVariable.update(uncheckedVars[i], varHeuristics[currIndexOfVarHeuristic].scoreOptimizedOf(uncheckedVars[i])))
						bestPos = i;
				Kit.swap(uncheckedVars, --nUncheckedVars, bestPos);
			}
			return bestScoredVariable.variable;
		}

		public Variable pick(Variable x) {
			assert uncheckedVars[nUncheckedVars
					- 1] == x : "should always be the case, because we always swap the selected variable with the one at the last position ";
			return uncheckedVars[--nUncheckedVars];
		}

		public void addLastVariable() {
			if (nUncheckedVars > 0 || uncheckedVars[0] == currSelectedVar)
				// otherwise,the last assigned variable was to keep building the branch, looking for a solution
				nUncheckedVars++;
		}

		private boolean controlUncheckedVariables() {
			IntStream.range(0, nUncheckedVars).forEach(i -> Kit.control(!uncheckedVars[i].isAssigned(), () -> uncheckedVars[i] + " is assigned"));
			return true;
		}
	}

	public ESAC3(Solver solver) {
		super(solver);
		this.queueESAC = new QueueESAC();
		this.varHeuristics = new HeuristicVariables[] { new WDegOnDom((SolverBacktrack) solver, false) };
		// this.variableOrderingHeuristics = new VariableOrderingHeuristic[] {
		// new Dom((BacktrackSearchSolver) solver, OptimizationType.MIN), new
		// DomThenDDeg((BacktrackSearchSolver) solver, OptimizationType.MIN),
		// new WDegOnDom((BacktrackSearchSolver) solver, OptimizationType.MAX)
		// };
		this.shavingEvaluator = cp().shaving.ratio != 0
				? new ShavingEvaluator(solver.pb.variables.length, cp().shaving.alpha, cp().shaving.ratio) : null;
	}

	private void makeSelection() {
		if (lastFailedVar == null || nBranchesBuilt < varHeuristics.length) {
			currSelectedVar = queueESAC.selectNextVariable();
			currSelectedIdx = currSelectedVar.dom.first();
		} else {
			currSelectedVar = queueESAC.pick(lastFailedVar);
			currSelectedIdx = lastFailedVar.dom.isPresent(lastFailedIdx) ? lastFailedIdx : lastFailedVar.dom.first();
		}
		lastFailedVar = null;
		assert !currSelectedVar.isAssigned() && currSelectedVar.dom.isPresent(currSelectedIdx) && queue.isEmpty();
	}

	protected boolean buildBranch() {
		// Kit.prn("building the branch number " + nbBuiltBranches + " queue size=" + queueESAC.nbUncheckedVariables);
		currIndexOfVarHeuristic = (currIndexOfVarHeuristic + 1) % varHeuristics.length;
		for (boolean finished = false; !finished;) {
			makeSelection();
			nSingletonTests++;
			solver.assign(currSelectedVar, currSelectedIdx);
			if (enforceArcConsistencyAfterAssignment(currSelectedVar)) {
				if (solver.depth() == solver.pb.variables.length) {
					solver.solManager.handleNewSolution(true);
					finished = true;
				}
			} else {
				queueESAC.addLastVariable();
				// Kit.prn("fail for " + selectedVariable + " last =" + (queueESAC.nbUncheckedVariables >0 ?
				// queueESAC.uncheckedVariables[queueESAC.nbUncheckedVariables - 1] :
				// ""));
				lastFailedVar = currSelectedVar;
				lastFailedIdx = currSelectedIdx;
				solver.backtrack(currSelectedVar);
				finished = !maximumBranchExtension || !canFindAnotherExtensionInsteadOf(currSelectedVar, currSelectedIdx);
			}
		}
		int lastBuiltBranchSize = solver.depth() - nodeDepth;
		if (lastBuiltBranchSize == 0)
			return manageInconsistentValue(currSelectedVar, currSelectedIdx);
		eraseLastBuiltBranch(lastBuiltBranchSize);
		return true;
	}

	@Override
	protected boolean enforceStrongConsistency() {
		nodeDepth = solver.depth();
		nBranchesBuilt = sumBranchSizes = 0;
		lastFailedVar = null;
		queueESAC.initialize();
		long nbEffectiveSingletonTestsBefore = nEffectiveSingletonTests;
		while (queueESAC.nUncheckedVars > 0) {
			performingProperSearch = true;
			boolean consistent = buildBranch();
			solver.resetNoSolutions();
			performingProperSearch = false;
			if (!consistent)
				return false;
			if (solver.finished())
				return true;
			// if (nbBuiltBranches > 1 && stopwatch.getCurrentWckTime() / 1000.0
			// > 40 && lastBuiltBranchSize > 0) {
			// OutputManager.printInfo("Stopping ESAC"); break; }
		}
		if (cp().verbose > 1)
			displayPassInfo(0, nEffectiveSingletonTests - nbEffectiveSingletonTestsBefore, true);
		return true;
	}
}
