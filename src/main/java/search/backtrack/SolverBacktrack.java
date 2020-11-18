/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package search.backtrack;

import static org.xcsp.common.Types.TypeFramework.COP;
import static utility.Kit.log;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.StringTokenizer;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.Constraint.CtrGlobal;
import executables.Resolution;
import heuristics.HeuristicValuesDynamic.Failures;
import heuristics.HeuristicVariables;
import interfaces.ObserverAssignment;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.ObserverConflicts;
import interfaces.ObserverRuns;
import interfaces.Optimizable;
import learning.LearnerNogoods;
import learning.LearnerStates;
import learning.NogoodMinimizer;
import propagation.Forward;
import search.Solver;
import search.statistics.Statistics.StatisticsBacktrack;
import utility.Enums.EBranching;
import utility.Enums.EStopping;
import utility.Kit;
import variables.DomainInfinite;
import variables.Variable;

public class SolverBacktrack extends Solver implements ObserverRuns, ObserverBacktrackingSystematic {

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
		stackedVariables.restoreBefore(depth);
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
			int p = t.length, n = pb.variables.length;
			Kit.control(1 < p && p <= n, () -> p + " vs " + n + (p == 1 ? " did you control the path for the file?" : ""));
			if (p < n) {
				Kit.log.warning("Missing values are completed with * (for presumably auxiliary variables). Is that correct?");
				t = Stream.concat(Stream.of(t), IntStream.range(0, n - p).mapToObj(i -> "*")).toArray(String[]::new);
			}
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
			return solManager.found > 0 && rs.cp.settingValh.solutionSaving;
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
	 * Classes for StackedVariables and Proofer
	 *********************************************************************************************/

	public final class StackedVariables {

		private SolverBacktrack solver;

		public final Variable[] stack;

		public int top = -1;

		public void reset() {
			top = -1;
		}

		public StackedVariables(SolverBacktrack solver, int size) {
			this.solver = solver;
			this.stack = new Variable[size];
		}

		// must be called before making modifications (e.g. for a variable, before reducing the domain of the variable)
		public void push(Variable observer) {
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
					Variable x = Stream.of(solver.pb.variables).filter(y -> !(y.dom instanceof DomainInfinite) && y.lastModificationDepth() >= depth)
							.findFirst().orElse(null);
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

		private boolean canCurrentlyPrint() {
			return active && !propagation.performingProperSearch && minDepthLimit <= depth() && depth() <= maxDepthLimit;
		}

		public void onBacktrack() {
			if (canCurrentlyPrint())
				log.fine("        Backtrack ");
		}

		public void onAssignment(Variable x, int a) {
			if (canCurrentlyPrint())
				log.fine("At " + depth() + ", " + x + " = " + x.dom.toVal(a) + (x.dom.indexesMatchValues() ? "" : " (index " + a + ") ")
						+ (x.dom.size() == 1 ? " singleton" : ""));
		}

		public void onRefutation(Variable x, int a) {
			if (canCurrentlyPrint())
				log.fine("At " + depth() + ", " + x + " != " + x.dom.toVal(a));
		}
	}

	/**********************************************************************************************
	 * Observers
	 *********************************************************************************************/

	@Override
	public void pushVariable(Variable x) {
		stackedVariables.push(x);
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
		if (rs.cp.settingSolving.enableSearch) {
			if (learnerNogoods != null && learnerNogoods.symmetryHandler != null)
				list.add((ObserverRuns) learnerNogoods.symmetryHandler);
			Stream.of(this, restarter, learnerStates, heuristicVars, lcReasoner, stats).filter(o -> o instanceof ObserverRuns)
					.forEach(o -> list.add((ObserverRuns) o));
		}
		Stream.of(pb.constraints).filter(c -> c instanceof ObserverRuns).forEach(c -> list.add((ObserverRuns) c));
		if (propagation instanceof ObserverRuns)
			list.add((ObserverRuns) propagation);
		list.add(rs.output);
		return list;
	}

	protected List<ObserverAssignment> collectObserversAssignment() {
		List<ObserverAssignment> list = new ArrayList<>();
		if (heuristicVars instanceof ObserverAssignment)
			list.add((ObserverAssignment) heuristicVars);
		return list;
	}

	protected List<ObserverConflicts> collectObserversPropagation() {
		List<ObserverConflicts> list = new ArrayList<>();
		if (heuristicVars instanceof ObserverConflicts)
			list.add((ObserverConflicts) heuristicVars);
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

	public final StackedVariables stackedVariables;

	public final List<ObserverBacktrackingSystematic> observersBacktrackingSystematic;

	public final RunProgressSaver runProgressSaver;

	public final WarmStarter warmStarter;

	public final Tracer tracer;

	public int minDepth, maxDepth;

	public NogoodMinimizer nogoodMinimizer;

	@Override
	public void reset() {
		super.reset();
		dr.reset();
		// if (!(heuristicVars instanceof HeuristicVariablesConflictBased) || !preserveWeightedDegrees)
		// heuristicVars.reset();
		heuristicVars.setPriorityVars(pb.priorityVars, 0);
		lcReasoner.beforeRun();
		if (learnerNogoods != null)
			learnerNogoods.reset();
		Kit.control(learnerStates == null);
		Kit.control(stackedVariables.top == -1, () -> "Top= " + stackedVariables.top);
		// Kit.control(observerCtrsSoft.top == -1);
		stats = new StatisticsBacktrack(this);
		Kit.control(!proofer.active);
	}

	public SolverBacktrack(Resolution resolution) {
		super(resolution);
		this.dr = new DecisionRecorder(this);
		this.heuristicVars = HeuristicVariables.buildFor(this);
		for (Variable x : pb.variables)
			x.buildValueOrderingHeuristic();
		this.lcReasoner = new LastConflictReasoner(this, resolution.cp.settingVarh.lastConflictSize);
		this.learnerNogoods = LearnerNogoods.buildFor(this); // may be null
		this.learnerStates = LearnerStates.buildFor(this); // may be null
		this.proofer = new Proofer(learnerStates);

		int nLevels = pb.variables.length + 1;
		int size = Stream.of(pb.variables).mapToInt(x -> x.dom.initSize()).reduce(0, (sum, domSize) -> sum + Math.min(nLevels, domSize));
		this.stackedVariables = new StackedVariables(this, size + nLevels);
		this.observersBacktrackingSystematic = collectObserversBacktrackingSystematic();
		this.observersRuns = collectObserversRuns();
		this.observersAssignment = collectObserversAssignment();
		this.observersConflicts = collectObserversPropagation();

		this.tracer = new Tracer(resolution.cp.settingGeneral.trace);
		this.stats = new StatisticsBacktrack(this);
		observersSearch.add(0, this.stats); // this list is initialized in the super-class

		this.runProgressSaver = resolution.cp.settingValh.runProgressSaving ? new RunProgressSaver() : null;
		this.warmStarter = resolution.cp.settingValh.warmStart.length() > 0 ? new WarmStarter(resolution.cp.settingValh.warmStart) : null;

		this.nogoodMinimizer = new NogoodMinimizer(this);
	}

	@Override
	public int depth() {
		return futVars.nDiscarded();
	}

	@Override
	public void assign(Variable x, int a) {
		assert !x.isAssigned();

		stats.nAssignments++;
		futVars.assign(x);
		x.doAssignment(a);
		dr.addPositiveDecision(x, a);
		for (ObserverAssignment obs : observersAssignment)
			obs.afterAssignment(x, a);
	}

	@Override
	public final void backtrack(Variable x) { // should we call it unassign or retract instead?
		int depthBeforeBacktrack = depth();
		futVars.unassign(x);
		x.undoAssignment();
		dr.delPositiveDecision(x);
		for (ObserverAssignment obs : observersAssignment)
			obs.afterUnassignment(x);
		for (ObserverBacktrackingSystematic obs : observersBacktrackingSystematic)
			obs.restoreBefore(depthBeforeBacktrack);
		if (propagation instanceof Forward)
			propagation.queue.clear();
	}

	@Override
	public final void backtrack() {
		backtrack(futVars.lastPast());
	}

	public final boolean tryAssignment(Variable x, int a) {
		tracer.onAssignment(x, a);
		stats.onAssignment(x);
		lcReasoner.onAssignment(x);
		assign(x, a);
		proofer.reset();
		boolean consistent = propagation.runAfterAssignment(x) && (learnerStates == null || learnerStates.dealWhenOpeningNode());
		if (x.heuristicVal instanceof Failures)
			((Failures) x.heuristicVal).updateWith(a, depth(), consistent);
		if (!consistent) {
			stats.nWrongDecisions++;
			stats.nFailedAssignments++;
			// if (learnerNogoods != null) learnerNogoods.addCurrentNogood();
			return false;
		}
		// if (stateRecordingManager != null && !stateRecordingManager.dealWhenOpeningNode()) return false;
		return true;
	}

	public final boolean tryAssignment(Variable x) {
		return tryAssignment(x, x.heuristicVal.bestIndex());
	}

	/**
	 * Called when an empty domain has been encountered.
	 */
	protected void manageEmptyDomainBeforeBacktracking() {
		if (runProgressSaver != null)
			runProgressSaver.manageEmptyDomainBeforeBacktracking();

		tracer.onBacktrack();
		stats.nBacktracks++;
		if (learnerStates != null)
			learnerStates.dealWhenClosingNode();
		if (futVars.nDiscarded() == 0)
			stoppingType = EStopping.FULL_EXPLORATION;
	}

	protected final boolean tryRefutation(Variable x, int a) {
		if (x.dom instanceof DomainInfinite)
			return false;
		tracer.onRefutation(x, a);
		stats.onRefutation(x);
		lcReasoner.onRefutation(x, a);
		dr.addNegativeDecision(x, a);
		proofer.recopy();
		x.dom.removeElementary(a);
		boolean consistent = x.dom.size() > 0;
		if (consistent) {
			if (rs.cp.settingSolving.branching == EBranching.NON)
				return true;
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
	private void manageContradiction(CtrGlobal objectiveToCheck) {
		for (boolean consistent = false; !consistent && stoppingType != EStopping.FULL_EXPLORATION;) {
			Variable x = futVars.lastPast();
			if (x == lastPastBeforeRun[nRecursiveRuns - 1] && !rs.cp.settingLNS.enabled)
				stoppingType = EStopping.FULL_EXPLORATION;
			else {
				int a = x.dom.unique();
				backtrack(x);
				consistent = tryRefutation(x, a) && propagation.propagate(objectiveToCheck);
			}
		}
	}

	/**
	 * This method allows to keep running the solver from the given level. Initially, this method is called from the level <code>0</code>. The principle of this
	 * method is to choose a variable and some values for this variable (maybe, all) until a domain becomes empty.
	 */
	public void explore() {
		maxDepth = 0;
		while (!finished() && !restarter.currRunFinished()) {
			while (!finished() && !restarter.currRunFinished()) {
				if (futVars.size() == 0)
					break;
				maxDepth = Math.max(maxDepth, depth());
				if (tryAssignment(heuristicVars.bestVar()) == false)
					manageContradiction(null);
			}
			if (futVars.size() == 0) {
				solManager.handleNewSolutionAndPossiblyOptimizeIt();
				CtrGlobal objectiveToCheck = pb.settings.framework == COP && !rs.cp.settingRestarts.restartAfterSolution ? (CtrGlobal) pb.optimizer.ctr : null;
				if (pb.settings.framework == COP && !rs.cp.settingRestarts.restartAfterSolution) {
					// first, we backtrack to the level where a value for a variable in the scope of the objective was removed for the last time
					objectiveToCheck = (CtrGlobal) pb.optimizer.ctr;
					((Optimizable) objectiveToCheck).setLimit(((Optimizable) objectiveToCheck).objectiveValue() + (pb.optimizer.minimization ? -1 : 1));
					int backtrackLevel = -1;
					for (int i = 0; i < objectiveToCheck.scp.length; i++) {
						int x = objectiveToCheck.futvars.dense[i]; // variables (of the objective) from the last assigned to the first assigned
						if (objectiveToCheck.scp[x].assignmentLevel() <= backtrackLevel)
							break;
						backtrackLevel = Math.max(backtrackLevel, objectiveToCheck.scp[x].dom.lastRemovedLevel());
					}
					assert backtrackLevel != -1;
					while (depth() > backtrackLevel)
						backtrack(futVars.lastPast());
					// check with java -ea ac /home/lecoutre/workspace/AbsCon/build/resources/main/cop/Photo.xml.lzma -cm -ev
					// java -ea ac /home/lecoutre/workspace/AbsCon/build/resources/main/cop/Recipe.xml.lzma -cm -
				}
				if (!finished() && !restarter.currRunFinished())
					manageContradiction(objectiveToCheck);
			}
		}
		minDepth = dr.minDepth(); // need to be recorded before backtracking to the root
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
		stackedVariables.restoreBefore(0);
		// we have to deal with definitively removed values
		// if (stoppingType != StoppingType.FULL_EXPLORATION) // pb with methods that need to restart
		observersBacktrackingSystematic.stream().forEach(obs -> obs.restoreBefore(0));

		dr.reset();
		// assert pb.stuff.nPurgedValues > 0 || Variable.areDomainsFull(pb.variables) : pb.stuff.nPurgedValues + " " + pb.nbValuesRemoved;
		// nPurged not updated; see java -ea abscon.Resolution problems.patt.QuasiGroup -data=6 -model=v5 -ev -cm=false
		assert Stream.of(pb.variables).allMatch(x -> x.dom.controlStructures());
	}

	@Override
	public final void solve() {
		super.solve();
		restoreProblem();
	}
}
