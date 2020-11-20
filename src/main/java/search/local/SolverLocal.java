/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.local;

import org.xcsp.common.Types.TypeFramework;

import main.Head;
import search.Solver;
import search.statistics.Statistics.StatisticsLocal;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

public final class SolverLocal extends Solver {

	protected final HeuristicNeighbors neighborHeuristic;

	public final ConflictManager conflictManager;

	protected StatisticsLocal localStatistics;

	public long nMinViolatedCtrs = Long.MAX_VALUE;

	public long nIterations;

	public int[] forcedInstantiation;

	public Variable[] decisionVars;

	/**
	 * Size : nbVars Values : -1 if the corresponding variable is not a decision variable its index in the successors array if the corresponding variable is a
	 * decision variable
	 */
	private int[] num2DecisionVarsIndex;

	/**
	 * For each decision variable v, we store an array containing all the indices of the variables that might be modified by propagating the dependency
	 * constraints after modifying v
	 */
	private int[][] successors;

	/**
	 * The inverse array, for each variable v we store the decision variable(s) which value modification can change v's value too by propagation
	 */

	private int[][] predecessors;

	/**
	 * For each dependency constraint, a FunctionalPropagator object is built to infer dependent variables
	 */
	protected FunctionalPropagator[] propagators;

	public SolverLocal(Head resolution) {
		super(resolution);
		this.neighborHeuristic = Reflector.buildObject(resolution.control.settingLocalSearch.classForNeighborHeuristic, HeuristicNeighbors.class, this);
		this.conflictManager = new ConflictManager(this);
		stats = this.localStatistics = new StatisticsLocal(this);
		this.nIterations = resolution.control.settingRestarts.cutoff == -2 ? 10 * problem.variables.length : resolution.control.settingRestarts.cutoff;
	}

	// @Override
	// protected final void doSearch() {
	// // initializeFunctionalPropagatorsAndVariablesLinks();
	// super.doSearch();
	// }

	private boolean[] forced;

	private int[] tmp;

	private int[] buildNewCompleteInstantiationFrom(int[] initialCompleteInstantiation, double bias) {
		assert problem.variables.length == initialCompleteInstantiation.length;
		Variable[] variables = problem.variables;
		if (forced == null) {
			forced = new boolean[variables.length];
			tmp = new int[variables.length];
		}
		long nPreservedValues = Math.round(bias * variables.length);
		for (int i = 0; i < nPreservedValues; i++) {
			int position = head.random.nextInt(variables.length);
			while (forced[position])
				position = head.random.nextInt(variables.length);
			tmp[position] = initialCompleteInstantiation[position];
			forced[position] = true;
		}
		for (int i = 0; i < variables.length; i++) {
			if (forced[i])
				continue;
			if (variables[i].dom.size() == 1)
				tmp[i] = variables[i].dom.unique();
			else {
				int a = variables[i].dom.random();
				while (a == initialCompleteInstantiation[i])
					a = variables[i].dom.random();
				tmp[i] = a;
			}
		}
		// for (int i = 0; i < variables.length; i++) tmp[i]
		// =(resolution.random.nextDouble() <
		// GlobalData.initialBiasForForcedSolution ? solution[i] :
		// variables[i].domain.getRandomIndex());
		return tmp;
	}

	private double initialBiasForForcedSolution = 0; // Data.initialBiasForForcedSolution

	protected void buildInitialCompleteInstantiation() {
		// if (forcedInstantiation == null && pb.api instanceof problems.rand.ExplicitRandomQuestion
		// && ((problems.rand.ExplicitRandomQuestion) pb.api).forcedSolution != null)
		// forcedInstantiation = ((problems.rand.ExplicitRandomQuestion) pb.api).forcedSolution;
		// else if (forcedInstantiation == null && problem instanceof problems.real.agapes.problem.AgapesProblem
		// && ((problems.real.agapes.problem.AgapesProblem) problem).getForcedSolution() != null)
		// forcedInstantiation = ((problems.real.agapes.problem.AgapesProblem) problem).getForcedSolution();
		if (forcedInstantiation != null)
			forcedInstantiation = initialBiasForForcedSolution > 0 ? buildNewCompleteInstantiationFrom(forcedInstantiation, initialBiasForForcedSolution)
					: forcedInstantiation;
		// Variable[] variables = pb.variables;
		// for (int i = 0; i < variables.length; i++)
		// if (variables[i].decision)
		// variables[i].dom.forcedIndex = forcedInstantiation != null ? forcedInstantiation[i] : variables[i].dom.random();

		// resolution.output.prn(forcedInstantiation);
		propagateDependentVariables();
		conflictManager.initializeConflictingConstraints();
		// conflictManager.displayConflictingConstraints();
	}

	public void propagateDependentVariables() {
		for (FunctionalPropagator propagator : propagators)
			propagator.propagate();
	}

	@Override
	public Solver doRun() {
		// if ((restarter.numRun + 1) % rs.cp.restarting.dataResetPeriod == 0 && rs.cp.hardCoding.weightingIncrementInConflictManager) {
		// Kit.log.fine("Reset weights");
		// for (Constraint c : pb.constraints)
		// c.resetWdeg();
		// }
		buildInitialCompleteInstantiation();
		for (int cnt = 1; cnt <= nIterations; cnt++) {
			// resolution.output.prn("rrr " + conflictManager.getNbConflictingConstraints());
			// if(conflictManager.getNbConflictingConstraints() == 9) {
			// problem.prettySolutionDisplay();
			// conflictManager.displayConflictingConstraints();
			// }
			if (conflictManager.nConflictingConstraints() == 0) {
				if (problem.settings.framework != TypeFramework.COP || problem.optimizer.value() < solManager.bestBound)
					solManager.handleNewSolution(true);
				if (!finished() && problem.settings.framework == TypeFramework.CSP)
					buildInitialCompleteInstantiation();
			}
			if (finished())
				break;
			neighborHeuristic.setBestNeighbor();
			// resolution.output.prn(conflictManager.getCurrentEvaluation());
			localStatistics.nAssignments++;

			// resolution.output.prn(conflictManager.getNbConflictingConstraints() + " conflicting constraints");
			if (conflictManager.nConflictingConstraints() == 0)
				Kit.log.fine("Current cost : " + problem.optimizer.value());

			if (conflictManager.nConflictingConstraints() < nMinViolatedCtrs) {
				nMinViolatedCtrs = conflictManager.nConflictingConstraints();
				// resolution.output.prn("o " + bestCostFound);
				// solutionManager.handleNewSolution();
				// resolution.output.prn("v " +
				// solutionManager.getLastSolutionFoundAsStringbuffer() + "\n");
				// if (upperBound == 0) setFullExploration(true);
				// if (upperBound == 1) { restarter.setNbRuns(0); break; }
			}
			if (cnt % 100 == 0)
				Kit.log.fine("\tconflicts=" + conflictManager.nConflictingConstraints() + "(" + conflictManager.currEvaluation() + "), upperBound="
						+ nMinViolatedCtrs + " time=" + head.instanceStopwatch.wckTime() + " nbIterations=" + cnt);
		}
		return this;
	}

	// private void initializeFunctionalPropagatorsAndVariablesLinks() {
	// List<Variable> decisionVarsList = new LinkedList<>();
	// for (Variable var : problem.variables)
	// if (var.decision)
	// decisionVarsList.add(var);
	// decisionVariables = decisionVarsList.toArray(new Variable[decisionVarsList.size()]);
	// successors = new int[decisionVariables.length][];
	//
	// List<CtrHard> dependencyConstraints = new LinkedList<>();
	// for (Constraint c : problem.constraints)
	// if (c instanceof CtrHard && ((CtrHard) c).getDependantVariablePosition() != -1)
	// dependencyConstraints.add((CtrHard) c);
	//
	// if (dependencyConstraints.size() > 0)
	// Kit.log.fine("\n\ttime=" + resolution.instanceStopwatch.getWckTime() + "\tInitializing functional propagators and variables
	// links.....");
	// propagators = new FunctionalPropagator[dependencyConstraints.size()];
	// int cnt = 0;
	// List<CtrHard> inferredConstraints = new LinkedList<>();
	// while (!dependencyConstraints.isEmpty()) {
	// for (CtrHard constraint : dependencyConstraints) {
	// boolean canCreateFunctionalPropagator = true;
	// for (int i = 0; i < constraint.scp.length; i++)
	// if (constraint.getDependantVariablePosition() != i) {
	// Variable independantVar = constraint.scp[i];
	// for (CtrHard otherConstraint : dependencyConstraints) {
	// if (constraint != otherConstraint && independantVar == otherConstraint.getDependantVariable()) {
	// canCreateFunctionalPropagator = false;
	// break;
	// }
	// }
	// if (!canCreateFunctionalPropagator)
	// break;
	// }
	// if (canCreateFunctionalPropagator) {
	// propagators[cnt++] = FunctionalPropagator.buildFunctionalPropagator(constraint, constraint.getDependantVariablePosition());
	// inferredConstraints.add(constraint);
	// }
	// }
	// dependencyConstraints.removeAll(inferredConstraints);
	// }
	//
	// List<List<Integer>> predecessorsList = new ArrayList<>(problem.variables.length);
	// id2DecisionVarsIndex = new int[problem.variables.length];
	// for (int i = 0; i < problem.variables.length; i++) {
	// predecessorsList.add(new ArrayList<Integer>());
	// id2DecisionVarsIndex[i] = -1;
	// }
	//
	// for (int i = 0; i < decisionVariables.length; i++) {
	// List<Integer> successorsList = new ArrayList<>();
	// successorsList.add(i);
	// predecessorsList.get(i).add(i);
	// for (int j = 0; j < successorsList.size(); j++) {
	// Variable current = problem.variables[successorsList.get(j)];
	// for (FunctionalPropagator propagator : propagators) {
	// int outputVarId = propagator.getCtr().getDependantVariable().num;
	// if (propagator.getCtr().involves(current) && propagator.getCtr().getDependantVariable() != current
	// && !successorsList.contains(outputVarId)) {
	// successorsList.add(outputVarId);
	// predecessorsList.get(outputVarId).add(i);
	// }
	// }
	// }
	// successors[i] = new int[successorsList.size()];
	// for (int j = 0; j < successorsList.size(); j++)
	// successors[i][j] = successorsList.get(j);
	// id2DecisionVarsIndex[problem.variables[i].num] = i;
	// }
	//
	// predecessors = new int[problem.variables.length][];
	// for (int i = 0; i < predecessors.length; i++) {
	// predecessors[i] = new int[predecessorsList.get(i).size()];
	// for (int j = 0; j < predecessors[i].length; j++)
	// predecessors[i][j] = predecessorsList.get(i).get(j);
	// }
	//
	// if (propagators.length > 0)
	// Kit.log.fine("\ttime=" + resolution.instanceStopwatch.getWckTime() + " initialization complete !");
	// }

	@Override
	public void pushVariable(Variable variable) {
	}

	@Override
	public int depth() {
		return 0;
	}

	@Override
	public void assign(Variable x, int a) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void backtrack(Variable x) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void backtrack() {
		throw new UnsupportedOperationException();
	}

	public int[] getSuccessors(int num) {
		return successors[num2DecisionVarsIndex[num]];
	}

	public int[] getPredecessors(int num) {
		return predecessors[num];
	}
}
