package solver.backtrack;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.Constraint;
import constraints.global.HammingProximityConstant.HammingProximityConstantGE;
import constraints.global.HammingProximityConstant.HammingProximityConstantSumLE;
import interfaces.FilteringSpecific;
import optimization.Optimizer.OptimizerDecreasing;
import problem.Problem;
import solver.Restarter;
import solver.Solver;
import solver.backtrack.RestarterLocalBranching.LocalBranchingConstraint.LBAtLeastEqual;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

public final class RestarterLocalBranching extends Restarter {

	private boolean currentlyBranching;

	private int nRestartsSinceActive;

	private LocalBranchingConstraint localBranchingConstraints;

	private int currDistance = solver.head.control.settingLB.baseDistance;

	public RestarterLocalBranching(Solver solver) {
		super(solver);
		Kit.control(solver instanceof SolverBacktrack, () -> "For local branching, only a SolverBacktrack can be used.");
		Kit.control(solver.problem.optimizer instanceof OptimizerDecreasing,
				() -> "For local branching, only OptimizationPilotDecreasing can be used.");

		this.localBranchingConstraints = solver.problem.symbolic != null
				? Reflector.buildObject(LBAtLeastEqual.class.getSimpleName(), LocalBranchingConstraint.class, solver.problem)
				: Reflector.buildObject(solver.head.control.settingLB.neighborhood, LocalBranchingConstraint.class, solver.problem);
		this.currDistance = solver.head.control.settingLB.baseDistance;
	}

	public void enterLocalBranching() {
		currentlyBranching = true;
		nRestartsSinceActive = 0;
	}

	private void leaveLocalBranching() {
		currentlyBranching = false;
		localBranchingConstraints.setIgnored(true);
		currDistance = solver.head.control.settingLB.baseDistance;
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
					currDistance = solver.head.control.settingLB.baseDistance;
				}
				localBranchingConstraints.updateWithNewSolution(solver.solManager.lastSolution, currDistance);
				localBranchingConstraints.setIgnored(false);
				((SolverBacktrack) solver).restoreProblem();
				if (((SolverBacktrack) solver).nogoodRecorder != null)
					((SolverBacktrack) solver).nogoodRecorder.reset();
				((FilteringSpecific) solver.problem.optimizer.ctr).runPropagator(null);
			}
			if (nRestartsSinceActive > solver.head.control.settingLB.maxRestarts)
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
		 * The non-objective variables' indexes
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
				c = (Constraint) ((CtrAlone) problem.tupleProximityGE(decisionVars, tuple, decisionVars.length - problem.head.control.settingLB.baseDistance,
						true)).ctr;
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
						problem.head.control.settingLB.baseDistance)).ctr;
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
