/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.Constraint;
import constraints.global.Extremum.ExtremumCst.MaximumCst.MaximumCstLE;
import constraints.global.HammingProximityConstant.HammingProximityConstantGE;
import constraints.global.HammingProximityConstant.HammingProximityConstantSumLE;
import constraints.global.ObjVar;
import dashboard.Control.SettingGeneral;
import dashboard.Control.SettingRestarts;
import interfaces.FilteringSpecific;
import interfaces.Observers.ObserverRuns;
import optimization.Optimizer.OptimizerDecreasing;
import problem.Problem;
import sets.SetDense;
import solver.Restarter.RestarterLB.LocalBranchingConstraint.LBAtLeastEqual;
import solver.backtrack.SolverBacktrack;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

/**
 * A restarter is used by a solver in order to manage restarts (successive runs from the root node).
 */
public class Restarter implements ObserverRuns {

	public static Restarter buildFor(Solver solver) {
		boolean lns = solver.head.control.lns.enabled;
		boolean lb = solver.head.control.lb.enabled;
		Kit.control(!lns || !lb, () -> "Cannot use LNS and LB at the same time.");
		if (lns)
			return new RestarterLNS((SolverBacktrack) solver);
		if (lb)
			return new RestarterLB(solver);
		return new Restarter(solver);
	}

	private long lubyCutoffFor(long i) {
		int k = (int) Math.floor(Math.log(i) / Math.log(2)) + 1;
		long pow = (long) Math.pow(2, k - 1);
		return i == pow * 2 - 1 ? pow : lubyCutoffFor(i - pow + 1);
	}

	@Override
	public void beforeRun() {
		numRun++;
		if (nRestartsSinceLastReset == setting.nRestartsResetPeriod) {
			nRestartsSinceLastReset = 0;
			baseCutoff = baseCutoff * setting.nRestartsResetCoefficient;
			Kit.log.info("BaseCutoff reset to " + baseCutoff);
		}
		if (forceRootPropagation || (settingsGeneral.framework == TypeFramework.COP && numRun - 1 == solver.solManager.lastSolutionRun)) {
			if (solver.propagation.runInitially() == false) // we run propagation if a solution has just been found (since the objective constraint has changed)
				solver.stopping = EStopping.FULL_EXPLORATION;
			forceRootPropagation = false;
			nRestartsSinceLastReset = 0;
		}
		if (currCutoff != Long.MAX_VALUE) {
			long offset = setting.luby ? lubyCutoffFor(numRun + 1) * 100 : (long) (baseCutoff * Math.pow(setting.factor, nRestartsSinceLastReset));
			currCutoff = measureSupplier.get() + offset;
		}
		nRestartsSinceLastReset++;
	}

	@Override
	public void afterRun() {
		if (settingsGeneral.framework == TypeFramework.COP)
			solver.problem.optimizer.afterRun();
	}

	/**
	 * The solver to which the restarter is attached.
	 */
	public Solver solver;

	/**
	 * The settings used for piloting the restarter (redundant field).
	 */
	private SettingRestarts setting;

	private SettingGeneral settingsGeneral;

	/**
	 * The measure used for handling cutoff values.
	 */
	public final Supplier<Long> measureSupplier;

	/**
	 * The number of the current run;
	 */
	public int numRun = -1;

	/**
	 * The base cutoff, and the current cutoff value as this value can evolve between successive runs.
	 */
	public long baseCutoff, currCutoff;

	public int nRestartsSinceLastReset;

	/**
	 * Set to true when running propagation from scratch at the root node must be made when a restart occurs.
	 */
	public boolean forceRootPropagation;

	public void reset() {
		numRun = -1;
		currCutoff = baseCutoff = setting.cutoff;
		nRestartsSinceLastReset = -1;
	}

	private Supplier<Long> measureSupplier() {
		SolverBacktrack sb = solver instanceof SolverBacktrack ? ((SolverBacktrack) solver) : null;
		switch (setting.measure) {
		case FAILED:
			return () -> sb.stats.nFailedAssignments;
		case WRONG:
			return () -> sb.stats.nWrongDecisions;
		case BACKTRACK:
			return () -> sb.stats.nBacktracks;
		case SOLUTION:
			return () -> solver.solManager.found;
		default:
			throw new AssertionError();
		}
	}

	public Restarter(Solver solver) {
		this.solver = solver;
		this.setting = solver.head.control.restarts;
		this.settingsGeneral = solver.head.control.general;
		this.measureSupplier = measureSupplier();
		if (settingsGeneral.framework == TypeFramework.COP)
			setting.cutoff *= 10;
		reset();
	}

	private long cnt;

	public boolean currRunFinished() {
		if (solver.problem.optimizer != null && ((cnt++) % 5) == 0)
			solver.problem.optimizer.possiblyUpdateLocalBounds();
		if (measureSupplier.get() >= currCutoff)
			return true;
		if (settingsGeneral.framework != TypeFramework.COP || numRun != solver.solManager.lastSolutionRun)
			return false;
		if (setting.restartAfterSolution)
			return true;
		if (solver.problem.optimizer.ctr instanceof MaximumCstLE || solver.problem.optimizer.ctr instanceof ObjVar)
			return true;
		return false;
	}

	/**
	 * Determines if there are no more (re)starts to perform.
	 */
	public boolean allRunsFinished() {
		return numRun + 1 >= setting.nRunsLimit;
	}

	public boolean runMultipleOf(int v) {
		return numRun > 0 && numRun % v == 0;
	}

	/**********************************************************************************************
	 * Subclasses (need to be fixed)
	 *********************************************************************************************/

	public final static class RestarterLNS extends Restarter {

		@Override
		public void beforeRun() {
			super.beforeRun();
			int[] solution = solver.solManager.lastSolution;
			if (solution != null) {
				heuristic.freezeVariables(solution);
				for (int i = heuristic.fragment.limit; i >= 0; i--) {
					Variable x = solver.problem.variables[i];
					solver.assign(x, solution[x.num]);
					boolean consistent = solver.propagation.runAfterAssignment(x);
					if (!consistent) {
						solver.backtrack(x);
						break;
					}
				}
			}
		}

		@Override
		public void afterRun() {
			((SolverBacktrack) solver).backtrackToTheRoot(); // because see Method doRun in SolverBacktrack
		}

		private final HeuristicFreezing heuristic;

		public RestarterLNS(SolverBacktrack solver) {
			super(solver);
			this.heuristic = HeuristicFreezing.buildFor(this);
		}

		// ************************************************************************
		// ***** Heuristics
		// ************************************************************************

		public static abstract class HeuristicFreezing {

			public static HeuristicFreezing buildFor(RestarterLNS restarter) {
				if (restarter.solver.head.control.lns.heuristic.equals("Impact"))
					return new Impact(restarter);
				else
					return new Rand(restarter);
			}

			protected final RestarterLNS restarter;

			public final SetDense fragment;

			public HeuristicFreezing(RestarterLNS restarter) {
				this.restarter = restarter;
				int n = restarter.solver.problem.variables.length;
				int nf = restarter.solver.head.control.lns.nFreeze, pf = restarter.solver.head.control.lns.pFreeze;
				this.fragment = new SetDense(n);
				int fragmentSize = 0 < nf && nf < n ? nf : 0 < pf && pf < 100 ? 1 + (pf * n) / 100 : -1;
				Kit.control(0 < fragmentSize && fragmentSize < n, () -> "You must specify the number or percentage of variables to freeze for LNS");
				this.fragment.limit = fragmentSize - 1;
			}

			// Implementing Fisher–Yates shuffle (see https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle)
			protected void shuffle() {
				Random random = restarter.solver.head.random;
				int[] dense = fragment.dense;
				for (int i = dense.length - 1; i > 0; i--) {
					int j = random.nextInt(i + 1);
					int tmp = dense[i];
					dense[i] = dense[j];
					dense[j] = tmp;
				}
			}

			public abstract void freezeVariables(int[] solution);

			public static class Impact extends HeuristicFreezing {

				private final Variable[] variables;

				private int[] before, after;

				public Impact(RestarterLNS restarter) {
					super(restarter);
					this.variables = restarter.solver.problem.variables;
					this.before = new int[variables.length];
					this.after = new int[variables.length];

				}

				private void storeDomainSizes(int[] t) {
					for (int i = 0; i < variables.length; i++)
						t[i] = variables[i].dom.size();
				}

				@Override
				public void freezeVariables(int[] solution) {
					shuffle();
					int[] dense = fragment.dense;
					Integer bestImpacted = null;
					for (int i = 0; i < fragment.size(); i++) {
						if (bestImpacted != null) {
							int tmp = dense[bestImpacted];
							dense[bestImpacted] = dense[i];
							dense[i] = tmp;
						}
						// else we automatically add the first element of shuffled (at position size)
						restarter.solver.assign(variables[dense[i]], solution[dense[i]]);

						storeDomainSizes(before);
						for (int x = 0; x < variables.length; x++)
							before[x] = variables[x].dom.size();
						restarter.solver.propagation.runInitially();
						for (int x = 0; x < variables.length; x++)
							after[x] = variables[x].dom.size();

						bestImpacted = null;
						int bestImpact = 0;
						for (int j = i + 1; j < dense.length; j++) {
							int impact = before[dense[j]] - after[dense[j]];
							if (impact > bestImpact) {
								bestImpacted = j;
								bestImpact = impact;
							}
						}
					}
					((SolverBacktrack) restarter.solver).backtrackToTheRoot();
				}
			}

			public static class Rand extends HeuristicFreezing {

				public Rand(RestarterLNS restarter) {
					super(restarter);
				}

				@Override
				public void freezeVariables(int[] solution) {
					shuffle();
				}
			}
		}
	}

	public static final class RestarterLB extends Restarter { // Local Branching

		private boolean currentlyBranching;

		private int nRestartsSinceActive;

		private LocalBranchingConstraint localBranchingConstraints;

		private int currDistance = solver.head.control.lb.baseDistance;

		public RestarterLB(Solver solver) {
			super(solver);
			Kit.control(solver instanceof SolverBacktrack, () -> "For local branching, only a SolverBacktrack can be used.");
			Kit.control(solver.problem.optimizer instanceof OptimizerDecreasing, () -> "For local branching, only OptimizationPilotDecreasing can be used.");

			this.localBranchingConstraints = solver.problem.symbolic != null
					? Reflector.buildObject(LBAtLeastEqual.class.getSimpleName(), LocalBranchingConstraint.class, solver.problem)
					: Reflector.buildObject(solver.head.control.lb.neighborhood, LocalBranchingConstraint.class, solver.problem);
			this.currDistance = solver.head.control.lb.baseDistance;
		}

		public void enterLocalBranching() {
			currentlyBranching = true;
			nRestartsSinceActive = 0;
		}

		private void leaveLocalBranching() {
			currentlyBranching = false;
			localBranchingConstraints.setIgnored(true);
			currDistance = solver.head.control.lb.baseDistance;
		}

		@Override
		public void beforeRun() {
			if (currentlyBranching)
				nRestartsSinceActive++;
			super.beforeRun();
		}

		@Override
		public void afterRun() {
			if (currentlyBranching) {
				if (solver.stopping == EStopping.FULL_EXPLORATION || forceRootPropagation) {
					Kit.control(solver.problem.stuff.nValuesRemovedAtConstructionTime == 0, () -> "Not handled for the moment");
					if (solver.stopping == EStopping.FULL_EXPLORATION) {
						solver.stopping = null;
						currDistance++;
						if (solver.problem.optimizer.areBoundsConsistent())
							forceRootPropagation = true;
					}
					if (forceRootPropagation) {
						super.afterRun();
						currDistance = solver.head.control.lb.baseDistance;
					}
					localBranchingConstraints.updateWithNewSolution(solver.solManager.lastSolution, currDistance);
					localBranchingConstraints.setIgnored(false);
					((SolverBacktrack) solver).restoreProblem();
					if (((SolverBacktrack) solver).nogoodRecorder != null)
						((SolverBacktrack) solver).nogoodRecorder.reset();
					((FilteringSpecific) solver.problem.optimizer.ctr).runPropagator(null);
				}
				if (nRestartsSinceActive > solver.head.control.lb.maxRestarts)
					leaveLocalBranching();
			} else {
				super.afterRun();
			}
		}

		public static abstract class LocalBranchingConstraint {

			/**
			 * The constraint which is posted when exploring a branch.
			 */
			protected Constraint c;

			/**
			 * The non-objective variables.
			 */
			protected final Variable[] decisionVars;

			/**
			 * The non-objective variables' positions
			 */
			private final int[] decisionVaps;

			public LocalBranchingConstraint(Problem pb) {
				// Variable[] objectiveVars = pb.stuff.stuffOptimization.collectedCostVarsFunctionalPropagatorsAtInit.stream().map(fp ->
				// fp.ctr.scp[fp.outputPos])
				// .toArray(Variable[]::new);

				decisionVars = Stream.of(pb.variables).toArray(Variable[]::new);
				decisionVaps = Kit.range(pb.variables.length);
				// List<Variable> decisionVarsList = new ArrayList<>();
				// List<Integer> decisionVapsList = new ArrayList<>();
				// for (int i = 0; i < pb.variables.length; i++)
				//
				// if (!Kit.isPresent(pb.variables[i], objectiveVars)) {
				// decisionVarsList.add(pb.variables[i]);
				// decisionVapsList.add(i);
				// }
				// decisionVars = decisionVarsList.toArray(new Variable[decisionVarsList.size()]);
				// decisionVaps = Kit.intArray(decisionVapsList);

				// Sort decisionVaps and decisionVars
				for (int i = 0; i < decisionVaps.length; i++) {
					int min = decisionVaps[i];
					int minPos = i;
					for (int j = i + 1; j < decisionVaps.length; j++) {
						if (decisionVaps[j] < min) {
							min = decisionVaps[j];
							minPos = j;
						}
					}
					if (minPos != i) {
						decisionVaps[minPos] = decisionVaps[i];
						decisionVaps[i] = min;
						Variable tmp = decisionVars[i];
						decisionVars[i] = decisionVars[minPos];
						decisionVars[minPos] = tmp;
					}
				}
			}

			/**
			 * Extracts an instantiation with vals of the decision variables from a complete instantiation with idxs.
			 * 
			 * @param completeInstantiationIdxs
			 *            : A complete instantiation (with idxs) of all the variables of the problem.
			 * @return An instantiation (with idxs) of the decision variables.
			 */
			public int[] toDecisionVals(int[] completeInstantiationIdxs) {
				List<Integer> decisionIdxs = new ArrayList<>();
				for (int i = 0; i < decisionVaps.length; i++)
					decisionIdxs.add(completeInstantiationIdxs[decisionVaps[i]]);
				int[] decisionVals = new int[decisionIdxs.size()];
				for (int i = 0; i < decisionVals.length; i++)
					decisionVals[i] = decisionVars[i].dom.toVal(decisionIdxs.get(i));
				return decisionVals;
			}

			public abstract void modifyConstraint(int[] decisionVals, int newDist);

			public void updateWithNewSolution(int[] instantiationIdxs, int newDist) {
				modifyConstraint(toDecisionVals(instantiationIdxs), newDist);
			}

			public boolean isDecisionVap(int vap) {
				return Arrays.binarySearch(decisionVaps, vap) >= 0;
			}

			public void setIgnored(boolean b) {
				c.ignored = b;
			}

			public static class LBAtLeastEqual extends LocalBranchingConstraint {

				public LBAtLeastEqual(Problem problem) {
					super(problem);
					int[] tuple = Stream.of(decisionVars).mapToInt(x -> x.dom.firstValue()).toArray();
					c = (Constraint) ((CtrAlone) problem.tupleProximityGE(decisionVars, tuple,
							decisionVars.length - problem.head.control.lb.baseDistance, true)).ctr;
					c.ignored = true;
				}

				@Override
				public void modifyConstraint(int[] decisionVals, int newDist) {
					((HammingProximityConstantGE) c).setTarget(decisionVals);
					((HammingProximityConstantGE) c).setK(newDist);
				}
			}

			public static class LBAtMostDistanceSum extends LocalBranchingConstraint {

				public LBAtMostDistanceSum(Problem problem) {
					super(problem);
					c = (Constraint) ((CtrAlone) problem.tupleProximityDistanceSum(decisionVars, new int[decisionVars.length],
							problem.head.control.lb.baseDistance)).ctr;
					c.ignored = true;
				}

				@Override
				public void modifyConstraint(int[] decisionVals, int newDist) {
					((HammingProximityConstantSumLE) c).setTarget(decisionVals);
					((HammingProximityConstantSumLE) c).setK(newDist);
				}
			}
		}
	}

}
