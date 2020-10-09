/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.backtrack;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import executables.Resolution;
import heuristics.values.HeuristicValuesDynamic.Failures;
import heuristics.variables.HeuristicVariables;
import heuristics.variables.dynamic.HeuristicVariablesConflictBased;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.ObserverPropagation;
import interfaces.ObserverRuns;
import interfaces.OptimizationCompatible;
import learning.LearnerNogoods;
import learning.LearnerStates;
import learning.LearnerStatesDominance;
import learning.LearnerStatesEquivalence;
import propagation.order1.AC;
import propagation.order1.PropagationForward;
import propagation.order1.inverse.GIC2;
import search.Solver;
import search.statistics.Statistics.StatisticsBacktrack;
import utility.Enums.EBranching;
import utility.Enums.ELearningNogood;
import utility.Enums.ELearningState;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Reflector;
import utility.sets.SetDense;
import variables.Variable;
import variables.domains.Domain;
import variables.domains.DomainHuge;

public class SolverBacktrack extends Solver implements ObserverRuns, ObserverBacktrackingSystematic {

	public int minDepth, maxDepth;

	@Override
	public void beforeRun() {
		if (runProgressSaver != null)
			runProgressSaver.beforeRun();
	}

	@Override
	public void afterRun() {
		if (runProgressSaver != null)
			runProgressSaver.afterRun();
	}

	@Override
	public void restoreBefore(int depth) {
		observerVars.restoreBefore(depth);
	}

	/**********************************************************************************************
	 * classes for warm starts and run progress saving
	 *********************************************************************************************/

	public class WarmStarter {
		public int[] sol;

		public WarmStarter(String s) {
			File file = new File(s);
			if (file.exists()) {
				try (BufferedReader in = new BufferedReader(new FileReader(s))) {
					StringBuilder sb = new StringBuilder();
					for (String line = in.readLine(); line != null; line = in.readLine())
						sb.append(line);
					s = sb.toString().trim();
				} catch (IOException e) {
					Kit.exit(e);
				}
			}
			String[] t = s.split(Constants.REG_WS);
			Kit.control(t.length == pb.variables.length,
					() -> t.length + " vs " + pb.variables.length + (t.length == 1 ? " did you control the path for the file?" : ""));
			this.sol = new int[t.length];
			for (int i = 0; i < sol.length; i++) {
				if (t[i].equals("*"))
					sol[i] = -1;
				else {
					int a = pb.variables[i].dom.toPresentIdx(Integer.parseInt(t[i]));
					Kit.control(a != -1);
					sol[i] = a;
				}
			}
		}

		public int valueOf(Variable x) {
			return sol[x.num];
		}
	}

	public class RunProgressSaver {
		int[] prevLongestRunBranch;
		int prevSize;
		int[] currLongestRunBranch;
		int currSize;

		RunProgressSaver() {
			this.prevLongestRunBranch = new int[pb.variables.length];
			this.currLongestRunBranch = new int[pb.variables.length];
		}

		boolean desactivated() {
			return solManager.nSolutionsFound > 0 && rs.cp.valh.bestSolution;
		}

		void manageEmptyDomainBeforeBacktracking() {
			if (desactivated())
				return;
			int d = depth(); // or Variable.nSingletonVariablesIn(pb.variables) ??
			if (d >= currSize) {
				currSize = d;
				for (int i = 0; i < prevLongestRunBranch.length; i++)
					prevLongestRunBranch[i] = pb.variables[i].dom.size() == 1 ? pb.variables[i].dom.unique() : -1;
				// System.out.println("new " + Kit.join(prevLongestRunBranch));
			}
		}

		void beforeRun() {
			minDepth = pb.variables.length + 1;
			maxDepth = 0;
			currSize = 0;
		}

		void afterRun() {
			if (desactivated())
				return;
			for (int i = 0; i < prevLongestRunBranch.length; i++)
				prevLongestRunBranch[i] = currLongestRunBranch[i];
			prevSize = currSize;
		}

		public int valueOf(Variable x) {
			return prevSize == 0 ? -1 : prevLongestRunBranch[x.num]; // prevSize == 0 means to be at the first run
		}
	}

	/**********************************************************************************************
	 * Intern class Tracer
	 *********************************************************************************************/

	public class Tracer {
		private boolean active;
		private int minDepthLimit, maxDepthLimit;

		private Tracer(String s) {
			active = s.length() != 0;
			StringTokenizer st = active && s.contains("-") ? new StringTokenizer(s, "-") : null;
			minDepthLimit = st != null && st.hasMoreTokens() ? Integer.parseInt(st.nextToken()) : Integer.MIN_VALUE;
			maxDepthLimit = st != null && st.hasMoreTokens() ? Integer.parseInt(st.nextToken()) : Integer.MAX_VALUE;
		}

		public void onBacktrack() {
			if (active && !propagation.performingProperSearch && minDepthLimit <= depth() && depth() <= maxDepthLimit)
				Kit.log.fine("        Backtrack ");
		}

		public void onAssignment(Variable x, int a) {
			if (active && !propagation.performingProperSearch && minDepthLimit <= depth() && depth() <= maxDepthLimit)
				Kit.log.fine("At " + depth() + ", " + x + " = " + a + (x.dom.indexesMatchValues() ? "" : "(" + x.dom.toVal(a) + ") ")
						+ (x.dom.size() == 1 ? " singleton" : ""));
		}

		public void onRefutation(Variable x, int a) {
			if (active && !propagation.performingProperSearch && minDepthLimit <= depth() && depth() <= maxDepthLimit)
				Kit.log.fine("At " + depth() + ", " + x + " != " + a);
		}
	}

	/**********************************************************************************************
	 * Observers
	 *********************************************************************************************/

	@Override
	public final void pushVariable(ObserverBacktrackingUnsystematic x) {
		observerVars.push(x);
	}

	private List<ObserverBacktrackingSystematic> collectObserversBacktrackingSystematic() {
		List<ObserverBacktrackingSystematic> list = new ArrayList<>();
		list.add(this); // because must be at first position in the list
		Stream.of(pb.constraints).filter(c -> c instanceof ObserverBacktrackingSystematic).forEach(c -> list.add((ObserverBacktrackingSystematic) c));
		if (propagation instanceof ObserverBacktrackingSystematic)
			list.add((ObserverBacktrackingSystematic) propagation);
		return list;
	}

	protected List<ObserverRuns> collectObserversRuns() {
		List<ObserverRuns> list = new ArrayList<>();
		Stream.of(this, restarter, learnerNogoods.symmetryHandler, learnerStates, heuristicVars, lcReasoner, stats).filter(o -> o instanceof ObserverRuns)
				.forEach(o -> list.add((ObserverRuns) o));
		Stream.of(pb.constraints).filter(c -> c instanceof ObserverRuns).forEach(c -> list.add((ObserverRuns) c));
		if (propagation instanceof ObserverRuns)
			list.add((ObserverRuns) propagation);
		list.add(rs.output);
		return list;
	}

	protected List<ObserverPropagation> collectObserversPropagation() {
		List<ObserverPropagation> list = new ArrayList<>();
		if (heuristicVars instanceof ObserverPropagation)
			list.add((ObserverPropagation) heuristicVars);
		return list;
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	public final DecisionRecorder dr;

	public HeuristicVariables heuristicVars;

	public final LastConflictReasoner lcReasoner;

	public final LearnerNogoods learnerNogoods;

	public final LearnerStates learnerStates;

	public final Proofer proofer;

	public final GlobalObserver observerVars;

	public final List<ObserverBacktrackingSystematic> observersBacktrackingSystematic;

	public final Tracer tracer;

	public StatisticsBacktrack backtrackStatistics;

	public final RunProgressSaver runProgressSaver;

	public final WarmStarter warmStarter;

	public final class GlobalObserver {

		private SolverBacktrack solver;

		public final ObserverBacktrackingUnsystematic[] stack;

		public int top = -1;

		public void reset() {
			top = -1;
		}

		public GlobalObserver(SolverBacktrack solver, int size) {
			this.solver = solver;
			this.stack = new ObserverBacktrackingUnsystematic[size];
		}

		// must be called before making modifications (e.g. for a variable, before reducing the domain of the variable)
		public void push(ObserverBacktrackingUnsystematic observer) {
			if (top == -1 || stack[top].lastModificationDepth() != solver.depth())
				stack[++top] = null; // null is used as a separator
			stack[++top] = observer;
		}

		public void restoreBefore(int depth) {
			if (top == -1 || stack[top].lastModificationDepth() < depth)
				return;
			for (; stack[top] != null; top--)
				stack[top].restoreBefore(depth);
			top--;
			assert controlStack(depth);
		}

		private boolean controlStack(int depth) {
			if (top >= 0 && stack[top] == null)
				return false;
			if (top >= 0)
				if (stack[top] instanceof Variable) {
					Variable x = Stream.of(solver.pb.variables).filter(y -> !(y.dom instanceof DomainHuge) && y.lastModificationDepth() >= depth).findFirst()
							.orElse(null);
					if (x != null) {
						System.out.println("Pb with " + x);
						x.dom.display(true);
						return false;
					}
				} else if (Stream.of(solver.pb.constraints).anyMatch(c -> c.extStructure() instanceof ObserverBacktrackingUnsystematic
						&& ((ObserverBacktrackingUnsystematic) c.extStructure()).lastModificationDepth() >= depth))
					return false;
			return true;
		}
	}

	public final class Proofer {
		private final boolean active;

		private final boolean[][] proofVariables;

		public Proofer(LearnerStates learner) {
			this.active = learner != null && learnerStates.reductionOperator.enablePElimination();
			this.proofVariables = this.active ? new boolean[pb.variables.length + 1][pb.variables.length] : null;
		}

		public boolean[] getProofVariablesAt(int depth) {
			return proofVariables[depth];
		}

		public void updateProof(Constraint c) {
			if (active)
				for (Variable x : c.scp)
					proofVariables[depth()][x.num] = true;
		}

		public void updateProof(int[] varNums) {
			if (active)
				for (int num : varNums)
					proofVariables[depth()][num] = true;
		}

		public void updateProofAll() {
			if (active)
				Arrays.fill(proofVariables[depth()], true);
		}

		public void reset() {
			if (active)
				Arrays.fill(proofVariables[depth()], false);
		}

		public void recopy() {
			if (active) {
				int d = depth();
				for (int i = pb.variables.length - 1; i >= 0; i--)
					if (proofVariables[d + 1][i])
						proofVariables[d][i] = true;
			}
		}
	}

	@Override
	public void reset(boolean preserveWeightedDegrees) {
		super.reset(preserveWeightedDegrees);
		dr.reset();
		if (!(heuristicVars instanceof HeuristicVariablesConflictBased) || !preserveWeightedDegrees)
			heuristicVars.reset();
		heuristicVars.setPriorityVars(pb.priorityVars, 0);
		lcReasoner.beforeRun();
		if (learnerNogoods != null)
			learnerNogoods.reset();
		Kit.control(learnerStates == null);
		Kit.control(observerVars.top == -1, () -> "Top= " + observerVars.top);
		// Kit.control(observerCtrsSoft.top == -1);
		stats = backtrackStatistics = new StatisticsBacktrack(this);
		Kit.control(!proofer.active);
	}

	public SolverBacktrack(Resolution resolution) {
		super(resolution);
		this.dr = new DecisionRecorder(this);
		Set<Class<?>> classes = resolution.handlerClasses.map.get(HeuristicVariables.class);
		this.heuristicVars = resolution.cp.settingSolving.enableSearch || propagation instanceof GIC2
				? Reflector.buildObject2(resolution.cp.varh.classForVarHeuristic, classes, this, resolution.cp.varh.anti)
				: null;
		this.lcReasoner = new LastConflictReasoner(this, resolution.cp.varh.lastConflictSize);
		if (heuristicVars != null)
			Stream.of(pb.variables).forEach(x -> x.buildValueOrderingHeuristic());

		this.learnerNogoods = resolution.cp.settingSolving.enableSearch && resolution.cp.settingLearning.nogood != ELearningNogood.NO
				&& propagation.queue != null ? new LearnerNogoods(this) : null;
		this.learnerStates = resolution.cp.settingLearning.state == ELearningState.EQUIVALENCE ? new LearnerStatesEquivalence(this)
				: resolution.cp.settingLearning.state == ELearningState.DOMINANCE ? new LearnerStatesDominance(this) : null;
		this.proofer = new Proofer(learnerStates);

		int nLevels = pb.variables.length + 1;
		int size = Stream.of(pb.variables).mapToInt(x -> x.dom.initSize()).reduce(0, (sum, domSize) -> sum + Math.min(nLevels, domSize));
		this.observerVars = new GlobalObserver(this, size + nLevels);
		this.observersBacktrackingSystematic = collectObserversBacktrackingSystematic();
		this.observersRuns = collectObserversRuns();
		this.observersPropagation = collectObserversPropagation();

		this.tracer = new Tracer(resolution.cp.settingGeneral.trace);
		this.stats = this.backtrackStatistics = new StatisticsBacktrack(this);
		observersSearch.add(0, this.stats);

		minimalNogoodExtractor = new MinimalNogoodExtractor();

		runProgressSaver = resolution.cp.valh.runProgressSaving ? new RunProgressSaver() : null;
		warmStarter = resolution.cp.valh.warmStart.length() > 0 ? new WarmStarter(resolution.cp.valh.warmStart) : null;
	}

	@Override
	public int depth() {
		return futVars.nDiscarded();
	}

	@Override
	public void assign(Variable x, int a) {
		assert !x.isAssigned();
		reduceWithUniversalValues();
		backtrackStatistics.nAssignments++;
		futVars.assign(x);
		x.doAssignment(a);
		dr.addPositiveDecision(x, a);
		for (ObserverPropagation obs : observersPropagation)
			obs.afterAssignment(x, a);
	}

	@Override
	public final void backtrack(Variable x) {
		int depthBeforeBacktrack = depth();
		futVars.unassign(x);
		x.undoAssignment();
		dr.delPositiveDecision(x);
		for (ObserverPropagation obs : observersPropagation)
			obs.afterUnassignment(x);

		for (ObserverBacktrackingSystematic obs : observersBacktrackingSystematic)
			obs.restoreBefore(depthBeforeBacktrack);
		if (propagation instanceof PropagationForward)
			propagation.queue.clear();
	}

	@Override
	public final void backtrack() {
		backtrack(futVars.lastPast());
	}

	/**
	 * Called when an empty domain has been encountered.
	 */
	protected void manageEmptyDomainBeforeBacktracking() {
		if (runProgressSaver != null)
			runProgressSaver.manageEmptyDomainBeforeBacktracking();

		tracer.onBacktrack();
		backtrackStatistics.nBacktracks++;
		if (learnerStates != null)
			learnerStates.dealWhenClosingNode();
		if (futVars.nDiscarded() == 0)
			stoppingType = EStopping.FULL_EXPLORATION;
	}

	public final boolean tryAssignment(Variable x, int a) {
		stats.nVisitedNodes++;
		if (x.dom.size() > 1)
			stats.nDecisions++;
		tracer.onAssignment(x, a);
		maxDepth = Math.max(maxDepth, depth());
		lcReasoner.doWhenAssignment(x);
		assign(x, a);
		proofer.reset();
		boolean consistent = propagation.runAfterAssignment(x) && (learnerStates == null || learnerStates.dealWhenOpeningNode());
		if (x.heuristicVal instanceof Failures)
			((Failures) x.heuristicVal).updateWith(a, depth(), consistent);
		if (!consistent) {
			stats.nWrongDecisions++;
			backtrackStatistics.nFailedAssignments++;
			// if (learnerNogoods != null) learnerNogoods.addCurrentNogood();
			// if (variableOrderingHeuristic instanceof Activity) ((Activity) variableOrderingHeuristic).update();
			return false;
		}
		// if (stateRecordingManager != null && !stateRecordingManager.dealWhenOpeningNode()) return false;
		return true;
	}

	public final boolean tryAssignment(Variable x) {
		return tryAssignment(x, x.heuristicVal.bestIndex());
	}

	protected final boolean tryRefutation(Variable x, int a) {
		if (x.dom instanceof DomainHuge)
			return false;

		tracer.onRefutation(x, a);
		minDepth = Math.min(minDepth, depth());

		lcReasoner.doWhenRefutation(x, a);
		dr.addNegativeDecision(x, a);
		proofer.recopy();
		x.dom.removeElementary(a);
		boolean consistent = x.dom.size() > 0;
		if (consistent) {
			if (rs.cp.settingSolving.branching == EBranching.NON)
				return true;
			stats.nVisitedNodes++;
			stats.nDecisions++;
			consistent = propagation.runAfterRefutation(x);
			if (!consistent)
				stats.nWrongDecisions++;
		}
		if (!consistent)
			manageEmptyDomainBeforeBacktracking();
		return consistent;
	}

	/**
	 * Called when a contradiction has been encountered.
	 */
	private void manageContradiction() {
		for (boolean consistent = false; !consistent && stoppingType != EStopping.FULL_EXPLORATION;) {
			Variable x = futVars.lastPast();
			if (x == lastPastBeforeRun[nRecursiveRuns - 1] && !rs.cp.settingLNS.enabled)
				stoppingType = EStopping.FULL_EXPLORATION;
			else {
				int a = x.dom.unique();
				backtrack(x);
				consistent = tryRefutation(x, a);
			}
		}
	}

	/**
	 * This method allows to keep running the solver from the given level. Initially, this method is called from the level <code>0</code>. The
	 * principle of this method is to choose a variable and some values for this variable (maybe, all) until a domain becomes empty.
	 */
	public void explore() {
		while (!finished() && !restarter.currRunFinished()) {
			while (!finished() && !restarter.currRunFinished()) {
				if (futVars.size() == 0)
					break;
				if (tryAssignment(heuristicVars.bestVar()) == false)
					manageContradiction();
			}
			if (futVars.size() == 0) {
				solManager.handleNewSolutionAndPossiblyOptimizeIt();
				if (rs.problem.framework == TypeFramework.COP && !rs.cp.settingRestarts.restartAfterSolution) {
					// we need to backtrack to the level where a value for a variable in the scope of the objective constraint has been removed
					// for
					// the last time
					Constraint c = (Constraint) rs.problem.optimizationPilot.ctr;
					((OptimizationCompatible) c).setLimit(((OptimizationCompatible) c).objectiveValue() + (rs.problem.optimizationPilot.minimization ? -1 : 1));
					int backtrackLevel = -1;
					for (int i = 0; i < c.scp.length; i++) {
						int x = c.futvars.dense[i];
						if (c.scp[x].assignmentLevel() <= backtrackLevel)
							break;
						backtrackLevel = Math.max(backtrackLevel, c.scp[x].dom.lastRemovedLevel());
					}
					assert backtrackLevel != -1;
					while (depth() != backtrackLevel)
						backtrack(futVars.lastPast());
				}
				if (!finished() && !restarter.currRunFinished()) {
					manageContradiction();
				}
			}
		}
		if (learnerNogoods != null && !finished() && !restarter.allRunsFinished())
			learnerNogoods.addNogoodsOfCurrentBranch();
	}

	private final Variable[] lastPastBeforeRun = new Variable[2];

	private int nRecursiveRuns = 0;

	@Override
	public Solver doRun() {
		lastPastBeforeRun[nRecursiveRuns++] = futVars.lastPast();
		explore();
		backtrackTo(lastPastBeforeRun[--nRecursiveRuns]);
		return this;
	}

	private void backtrackTo(Variable x) {
		assert x == null || x.isAssigned();
		while (futVars.lastPast() != x)
			backtrack(futVars.lastPast());
	}

	public void backtrackToTheRoot() {
		backtrackTo(null);
	}

	/**
	 * Called in order to get the problem back in its initial state.
	 */
	public final void restoreProblem() {
		backtrackToTheRoot();
		// we also undo preprocessing propagation
		observerVars.restoreBefore(0);
		// we have to deal with definitively removed values
		// if (stoppingType != StoppingType.FULL_EXPLORATION) // pb with methods that need to restart
		observersBacktrackingSystematic.stream().forEach(obs -> obs.restoreBefore(0));

		dr.reset();
		// assert pb.stuff.nPurgedValues > 0 || Variable.areDomainsFull(pb.variables) : pb.stuff.nPurgedValues + " " + pb.nbValuesRemoved;
		// // nPurged not updated
		// see java -ea abscon.Resolution problems.patt.QuasiGroup -data=6 -model=v5 -ev -cm=fals
		assert Stream.of(pb.variables).allMatch(x -> x.dom.controlStructures());
	}

	@Override
	public final void solve() {
		super.solve();
		restoreProblem();
	}

	// public final int mark() {
	// assert observerCtrsSoft.stack.length == 0;
	// setDomainsMarks();
	// for (ObserverBacktrackingSystematic obs : observersBacktrackingSystematic)
	// obs.setMark();
	// return observerVars.top;
	// }
	//
	// public final void unmark(int top) {
	// assert observerCtrsSoft.stack.length == 0;
	// for (ObserverBacktrackingSystematic obs : observersBacktrackingSystematic)
	// obs.restoreAtMark();
	// restoreDomainsAtMarks();
	// observerVars.top = top;
	// }

	/**********************************************************************************************
	 * Start of experimental section
	 *********************************************************************************************/

	// experimental
	private void reduceWithUniversalValues() {
		boolean test = false;
		if (test)
			for (Variable x : pb.variables) {
				Domain dom = x.dom;
				if (dom.size() == 1)
					continue;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					boolean universal = true;
					for (Constraint ctr : x.ctrs) {
						boolean found = false;
						for (Variable y : ctr.scp) {
							if (y == x)
								continue;
							if (!y.dom.isPresent(a))
								found = true;
						}
						if (!found) {
							universal = false;
							break;
						}
					}
					if (universal) {
						x.dom.reduceTo(a);
					}
				}
			}
	}

	public int doGreedy(int[] vids, int[] idxs, int limit) {
		int i = 0, max = limit;
		Variable[] variables = pb.variables;
		for (; i <= max; i++) {
			if (!variables[vids[i]].dom.isPresent(idxs[i]))
				break;
			assign(variables[vids[i]], idxs[i]);
			if (!propagation.runAfterAssignment(variables[vids[i]]))
				break;
		}
		if (i > limit)
			i--;
		backtrackToTheRoot();
		// restoreProblem();
		return i; // limit;
	}

	public MinimalNogoodExtractor minimalNogoodExtractor;

	public class MinimalNogoodExtractor {

		private boolean addPositiveTransitionDecisionTo(int positiveDecision, int[] tmp, int nbFoundTransitionDecisions) {
			tmp[nbFoundTransitionDecisions] = positiveDecision;
			Variable var = dr.varIn(positiveDecision);
			int idx = dr.idxIn(positiveDecision);
			if (!var.dom.isPresent(idx))
				return false;
			assign(var, idx);
			return propagation.runAfterAssignment(var);
		}

		private int searchPositiveTransitionDecision(int right, int[] decs, int limitDepth) {
			boolean consistent = true;
			int left = 0;
			for (; consistent && left < right; left++) {
				Variable var = dr.varIn(decs[left]);
				int idx = dr.idxIn(decs[left]);
				if (!var.dom.isPresent(idx)) {
					consistent = false;
				} else {
					assign(var, idx);
					consistent = propagation.runAfterAssignment(var);
				}
				assert !consistent || !(propagation instanceof AC) || ((AC) propagation).controlArcConsistency();
			}
			if (consistent)
				return -1;
			while (futVars.size() > 0 && depth() != limitDepth - 1)
				backtrack();
			// for (Variable var = futVars.lastPast(); var != null; var = futVars.prevPast(var))
			// if (getDepth() == limitDepth - 1)
			// break;
			// else
			// backtrack(var);
			return left - 1;
		}

		public int[] extractMinimalNogoodFrom(int[] decs) {
			int[] tmp = new int[decs.length];
			int positionOfLastFoundTransitionDecision = decs.length - 1; // right excluded
			int nbFoundTransitionDecisions = 0;
			boolean backgroundConsistent = addPositiveTransitionDecisionTo(decs[positionOfLastFoundTransitionDecision], tmp, nbFoundTransitionDecisions++);
			if (!backgroundConsistent) {
				Variable x = futVars.lastPast();
				int a = x.dom.unique();
				backtrack(x);
				x.dom.removeElementary(a);
				// Kit.prn("Nogood size 1");
				backgroundConsistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
				if (!backgroundConsistent) {
					stoppingType = EStopping.FULL_EXPLORATION;
					return new int[0];
				}
				return null;
			}
			while (backgroundConsistent && 0 < positionOfLastFoundTransitionDecision && nbFoundTransitionDecisions < rs.cp.settingLearning.nogoodArityLimit) {
				if (positionOfLastFoundTransitionDecision == 1) {
					tmp[nbFoundTransitionDecisions++] = decs[0];
					break;
				}
				positionOfLastFoundTransitionDecision = searchPositiveTransitionDecision(positionOfLastFoundTransitionDecision, decs, depth());
				if (positionOfLastFoundTransitionDecision != -1)
					backgroundConsistent = addPositiveTransitionDecisionTo(decs[positionOfLastFoundTransitionDecision], tmp, nbFoundTransitionDecisions++);
			}
			backtrackToTheRoot();

			// if (consistent && nbFoundTransitionDecisions >=
			// NogoodManager.NOGOOD_SIZE_LIMIT || (right == -1 && nbDecisions >=
			// NogoodManager.NOGOOD_SIZE_LIMIT))
			// return null;

			if (positionOfLastFoundTransitionDecision == -1) {
				int[] t = new int[decs.length];
				for (int i = 0; i < t.length; i++)
					t[i] = -decs[i];
				return t;
			} else {
				// Kit.prn("Nogood reduction from " + decisions.length + " to "
				// + nbFoundTransitionDecisions);
				int[] t = new int[nbFoundTransitionDecisions];
				for (int i = 0; i < t.length; i++)
					t[i] = -tmp[i];
				return t;
			}
		}

		// ****************************************/

		private boolean addTransitionDecisionTo(int indexOfLastTransitionDecision, int[] tmp, int nbFoundTransitionDecisions, int[] decs, int nbDecs) {
			tmp[nbFoundTransitionDecisions] = decs[indexOfLastTransitionDecision];
			int limit = Math.max(0, nbFoundTransitionDecisions - 1);
			while (tmp[limit] < 0)
				limit--;
			for (int i = limit; i < nbFoundTransitionDecisions; i++) {
				Variable var = dr.varIn(tmp[i]);
				int idx = dr.idxIn(tmp[i]);
				if (tmp[i] > 0) {
					assert var.dom.isPresent(idx);
					assign(var, idx);
					boolean consistent = propagation.runAfterAssignment(var);
					assert consistent;
				} else {
					assert var.dom.size() > 1 || !var.dom.isPresent(idx);
					if (var.dom.isPresent(idx)) {
						var.dom.removeElementary(idx);
						boolean consistent = var.dom.size() > 0 && propagation.runAfterRefutation(var);
						assert consistent;
					}
				}
			}
			Variable var = dr.varIn(decs[indexOfLastTransitionDecision]);
			int idx = dr.idxIn(decs[indexOfLastTransitionDecision]);
			boolean consistent = true;
			if (decs[indexOfLastTransitionDecision] > 0) {
				if (!var.dom.isPresent(idx))
					return false;
				assign(var, idx);
				consistent = propagation.runAfterAssignment(var);
			} else {
				if (var.dom.size() == 1 && var.dom.isPresent(idx))
					return false;
				if (var.dom.isPresent(idx)) {
					var.dom.removeElementary(idx);
					consistent = var.dom.size() > 0 && propagation.runAfterRefutation(var);
				}
			}
			return consistent;
		}

		/**
		 * Returns the index in decisions of the transition decision, or -1 if it is not found. It is possible since we just use the original
		 * constraints of the problem and not the noggods recorded so far (it ssem rather difficult).
		 */
		private int searchTransitionDecision(int left, int right, int[] decs, int nbDecs, int limitDepth) {
			boolean consistent = true;
			for (; left < right && consistent; left++) {
				Variable x = dr.varIn(decs[left]);
				int a = dr.idxIn(decs[left]);
				if (decs[left] > 0) {
					if (!x.dom.isPresent(a)) {
						consistent = false;
					} else {
						assign(x, a);
						consistent = propagation.runAfterAssignment(x);
					}
				} else {
					if (x.dom.size() == 1 && x.dom.isPresent(a))
						consistent = false;
					else if (x.dom.isPresent(a)) {
						x.dom.removeElementary(a);
						consistent = x.dom.size() > 0 && propagation.runAfterRefutation(x);
					}
				}
				assert !consistent || !(propagation instanceof AC) || ((AC) propagation).controlArcConsistency();
			}
			if (left == nbDecs - 1 && consistent)
				return -1;
			assert !consistent && (left - 1) < right : "cons = " + consistent + " lastPositive = " + (left - 1);
			while (futVars.size() > 0 && depth() != limitDepth - 1)
				backtrack();
			// for (Variable y = futVars.lastPast(); y != null; y = futVars.prevPast(y))
			// if (getDepth() == limitDepth - 1)
			// break;
			// else
			// backtrack(y);
			return left - 1;
		}

		public int[] extractMinimalNogoodFrom(SolverBacktrack solver, int[] decs, int nbDecs) {
			propagation.queue.clear();
			Variable[] variables = pb.variables;
			// copy of the original problem at depth 0 : it means that all
			// negative decisions that occur before the first positive one have
			// been taken into account
			for (int i = 0; i < variables.length; i++) {
				Domain dom = solver.pb.variables[i].dom;
				for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a))
					if (dom.isRemovedAtLevel(a, 0))
						variables[i].dom.remove(a, 0);
			}
			int[] tmp = new int[nbDecs];
			int nbFoundTransitionDecisions = 0;
			boolean consistent = addTransitionDecisionTo(nbDecs - 1, tmp, nbFoundTransitionDecisions++, decs, nbDecs);
			int initialLeftOffset = 0;
			while (decs[initialLeftOffset] < 0)
				initialLeftOffset++;
			int right = nbDecs - 1; // right excluded
			while (consistent && nbFoundTransitionDecisions < rs.cp.settingLearning.nogoodArityLimit && initialLeftOffset < right) {
				assert decs[initialLeftOffset] > 0;
				int IndexOfTransitionDecision = searchTransitionDecision(initialLeftOffset, right, decs, nbDecs, depth());
				if (IndexOfTransitionDecision == -1)
					right = -1;
				else {
					right = IndexOfTransitionDecision;
					consistent = addTransitionDecisionTo(IndexOfTransitionDecision, tmp, nbFoundTransitionDecisions++, decs, nbDecs);
				}
			}
			restoreProblem();
			if (consistent && nbFoundTransitionDecisions >= rs.cp.settingLearning.nogoodArityLimit
					|| (right == -1 && nbDecs >= rs.cp.settingLearning.nogoodArityLimit))
				return null;
			int[] nogood = null;
			if (right == -1) {
				int nbPositiveDecisions = 0;
				for (int i = 0; i < nbDecs; i++)
					if (decs[i] > 0)
						nbPositiveDecisions++;
				nogood = new int[nbPositiveDecisions + 2];
				int cnt = 2;
				for (int i = 0; i < nbDecs; i++)
					if (decs[i] > 0)
						nogood[cnt++] = -decs[i];
			} else {
				nogood = new int[nbFoundTransitionDecisions + 2];
				for (int i = 2; i < nogood.length; i++)
					nogood[i] = -tmp[i - 2];
			}
			assert controlMinimalNogood(solver, nogood);
			return nogood;
		}

		public int[] extractMinimalNogoodFrom(SolverBacktrack solver, SetDense denseSet) {
			return extractMinimalNogoodFrom(solver, denseSet.dense, denseSet.size());
		}

		public boolean controlMinimalNogood(SolverBacktrack solver, int[] t) {
			if (t == null)
				return true;
			propagation.queue.clear();
			// copy of the original problem at depth 0 : it means that all
			// negative decisions that occur befor the first positive one have
			// been taken into account
			for (int i = 0; i < pb.variables.length; i++) {
				Domain dom = solver.pb.variables[i].dom, auxiliaryDom = pb.variables[i].dom;
				for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a))
					if (dom.isRemovedAtLevel(a, 0))
						auxiliaryDom.remove(a, 0);
			}
			boolean notMinimal = false;
			for (int i = 2; !notMinimal && i < t.length; i++) {
				int decision = -t[i];
				Variable var = dr.varIn(decision);
				int idx = dr.idxIn(decision);
				if (decision > 0) {
					if (!var.dom.isPresent(idx)) {
						if (i != t.length - 1) {
							Kit.log.info("nogood not minimal 1 " + var + " " + idx);
							notMinimal = true;
						}
					} else {
						assign(var, idx);
						boolean consistent = propagation.runAfterAssignment(var);
						if (!consistent && i != t.length - 1) {
							Kit.log.info("nogood not minimal 2 " + var + " " + idx);
							notMinimal = true;
						}
					}
				} else {
					if (var.dom.size() == 1 && var.dom.isPresent(idx)) {
						if (i != t.length - 1) {
							Kit.log.info("nogood not minimal 3 " + var + " " + idx);
							notMinimal = true;
						}
					} else if (var.dom.isPresent(idx)) {
						var.dom.removeElementary(idx);
						boolean consistent = var.dom.size() > 0 && propagation.runAfterRefutation(var);
						if (!consistent && i != t.length - 1) {
							Kit.log.info("nogood not minimal 4 " + var + " " + idx);
							notMinimal = true;
						}
					}
				}
			}
			restoreProblem();
			return !notMinimal;
		}
	}

	/**********************************************************************************************
	 * End of experimental section
	 *********************************************************************************************/
}
