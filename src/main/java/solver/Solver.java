/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package solver;

import static java.util.stream.Collectors.toCollection;
import static org.xcsp.common.Types.TypeFramework.COP;
import static utility.Enums.Stopping.EXCEEDED_TIME;
import static utility.Enums.Stopping.FULL_EXPLORATION;
import static utility.Kit.control;
import static utility.Kit.log;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.StringTokenizer;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.ConstraintGlobal;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDynamic.Bivs;
import heuristics.HeuristicVariables;
import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Observers.ObserverOnConflicts;
import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRemovals;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolving;
import learning.IpsRecorder;
import learning.NogoodMinimizer;
import learning.NogoodRecorder;
import main.Head;
import problem.Problem;
import propagation.Forward;
import propagation.Propagation;
import sets.SetDense;
import sets.SetSparseReversible;
import utility.Enums.Branching;
import utility.Enums.Stopping;
import utility.Kit;
import variables.DomainInfinite;
import variables.Variable;

public class Solver implements ObserverOnRuns, ObserverOnBacktracksSystematic {

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
		entailed.restoreLimitAtLevel(depth);
	}

	/**********************************************************************************************
	 * classes for warm starts and run progress saving
	 *********************************************************************************************/

	public final class WarmStarter {
		int[] sol;

		private String[] possiblyDecompact(String[] t) {
			List<String> list = null;
			for (int i = 0; i < t.length; i++) {
				boolean compact = t[i].contains(Constants.TIMES);
				if (compact && list == null) {
					list = new ArrayList<>();
					for (int j = 0; j < i; j++)
						list.add(t[j]);
				}
				if (list != null) {
					if (compact) {
						String[] tmp = t[i].split(Constants.TIMES);
						assert tmp.length == 2;
						for (int j = Integer.parseInt(tmp[1]) - 1; j >= 0; j--)
							list.add(tmp[0]);
					} else
						list.add(t[i]);
				}
			}
			return list != null ? list.stream().toArray(String[]::new) : t;
		}

		WarmStarter(String s) {
			File file = new File(s);
			if (file.exists()) { // TODO if the string starts with ~/, that does not work (the path must be explicit)
				try (BufferedReader in = new BufferedReader(new FileReader(s))) {
					StringBuilder sb = new StringBuilder();
					for (String line = in.readLine(); line != null; line = in.readLine())
						sb.append(line);
					s = sb.toString().trim();
				} catch (IOException e) {
					Kit.exit(e);
				}
			}
			String[] t = possiblyDecompact(s.split(Constants.REG_WS));
			int p = t.length, n = problem.variables.length;
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
					int a = problem.variables[i].dom.toIdxIfPresent(Integer.parseInt(t[i]));
					Kit.control(a != -1, "pb with " + problem.variables[i] + " and " + t[i]);
					sol[i] = a;
				}
			}
		}

		public int valueOf(Variable x) {
			return sol[x.num];
		}
	}

	public final class RunProgressSaver {
		int[] prevLongestRunBranch;
		int prevSize;
		int[] currLongestRunBranch;
		int currSize;

		RunProgressSaver() {
			this.prevLongestRunBranch = new int[problem.variables.length];
			this.currLongestRunBranch = new int[problem.variables.length];
		}

		boolean desactivated() {
			return solutions.found > 0 && head.control.valh.solutionSaving;
		}

		void manageEmptyDomainBeforeBacktracking() {
			if (desactivated())
				return;
			int d = depth(); // or Variable.nSingletonVariablesIn(pb.variables) ??
			if (d >= currSize) {
				currSize = d;
				for (int i = 0; i < prevLongestRunBranch.length; i++)
					prevLongestRunBranch[i] = problem.variables[i].dom.size() == 1 ? problem.variables[i].dom.single() : -1;
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

	public static int cnt = 0;

	/**
	 * The object for recording which variables are modified (i.e., with a reduced domain) at each level of search
	 */
	public final class StackedVariables {

		public final Variable[] stack;

		public int top = -1;

		public StackedVariables(int size) {
			this.stack = new Variable[size];
		}

		// must be called before making modifications (i.e. before reducing the domain of the variable)
		public int push(Variable x) {
			int depth = depth();
			assert x.dom.lastRemovedLevel() <= depth;
			if (x.dom.lastRemovedLevel() != depth) { // because, otherwise, already present
				if (top == -1 || stack[top].dom.lastRemovedLevel() != depth)
					stack[++top] = null; // null is used as a separator
				stack[++top] = x;
			}
			return depth;
		}

		public void restoreBefore(int depth) {
			if (top == -1 || stack[top].dom.lastRemovedLevel() < depth)
				return;
			for (; stack[top] != null; top--)
				stack[top].restoreBefore(depth);
			top--;
			assert controlStack(depth);
		}

		private boolean controlStack(int depth) {
			if (top < -1)
				return false;
			if (top == -1)
				return true;
			if (stack[top] == null)
				return false;
			Variable x = Stream.of(problem.variables).filter(y -> !(y.dom instanceof DomainInfinite) && y.dom.lastRemovedLevel() >= depth).findFirst()
					.orElse(null);
			if (x != null) {
				System.out.println("Pb with " + x);
				x.dom.display(true);
				return false;
			}
			return true;
		}
	}

	public final class Proofer implements ObserverOnDecisions {

		public final boolean[][] proofVariables;

		public Proofer() {
			this.proofVariables = new boolean[problem.variables.length + 1][problem.variables.length];
		}

		public void updateProof(Constraint c) {
			for (Variable x : c.scp)
				proofVariables[depth()][x.num] = true;
		}

		public void updateProof(int[] nums) {
			for (int num : nums)
				proofVariables[depth()][num] = true;
		}

		public void updateProofAll() {
			Arrays.fill(proofVariables[depth()], true);
		}

		@Override
		public void beforePositiveDecision(Variable x, int a) { // reset
			Arrays.fill(proofVariables[depth() + 1], false); // +1 because the assignment has not yet been made
		}

		@Override
		public void beforeNegativeDecision(Variable x, int a) { // recopy
			int d = depth();
			for (int i = problem.variables.length - 1; i >= 0; i--)
				if (proofVariables[d + 1][i])
					proofVariables[d][i] = true;
		}

	}

	/**********************************************************************************************
	 * Intern class Tracer
	 *********************************************************************************************/

	public final class Tracer implements ObserverOnDecisions {
		private int minDepthLimit, maxDepthLimit;

		private Tracer(String s) {
			StringTokenizer st = s.contains("-") ? new StringTokenizer(s, "-") : null;
			minDepthLimit = st != null && st.hasMoreTokens() ? Integer.parseInt(st.nextToken()) : Integer.MIN_VALUE;
			maxDepthLimit = st != null && st.hasMoreTokens() ? Integer.parseInt(st.nextToken()) : Integer.MAX_VALUE;
		}

		private boolean canCurrentlyPrint() {
			return !propagation.performingProperSearch && minDepthLimit <= depth() && depth() <= maxDepthLimit;
		}

		public void onBacktrack() {
			if (canCurrentlyPrint())
				log.fine("        Backtrack ");
		}

		@Override
		public void beforePositiveDecision(Variable x, int a) {
			if (canCurrentlyPrint())
				log.fine("At " + depth() + ", " + x + " = " + x.dom.toVal(a) + (x.dom.indexesMatchValues() ? "" : " (index " + a + ") ")
						+ (x.dom.size() == 1 ? " singleton" : ""));
		}

		@Override
		public void beforeNegativeDecision(Variable x, int a) {
			if (canCurrentlyPrint())
				log.fine("At " + depth() + ", " + x + " != " + x.dom.toVal(a));
		}
	}

	/**********************************************************************************************
	 * Section about attached observers
	 *********************************************************************************************/

	/**
	 * The list of observers on the main solving steps of the solver
	 */
	public final List<ObserverOnSolving> observersOnSolving;

	/**
	 * The list of observers on successive runs executed by the solver
	 */
	public final List<ObserverOnRuns> observersOnRuns;

	/**
	 * The list of observers (that are systematically executed) on backtracks
	 */
	public final List<ObserverOnBacktracksSystematic> observersOnBacktracksSystematic;

	/**
	 * The list of observers on decisions taken by the solver
	 */
	public List<ObserverOnDecisions> observersOnDecisions;

	/**
	 * The list of observers on (explicitly) assignments performed by the solver
	 */
	public final List<ObserverOnAssignments> observersOnAssignments;

	/**
	 * The list of observers on removals, i.e., value deletions in domains. Whenever a domain is reduced, a callback function is called.
	 */
	public final Collection<ObserverOnRemovals> observersOnRemovals = new ArrayList<>();

	/**
	 * The list of observers on conflicts encountered during search
	 */
	public final List<ObserverOnConflicts> observersOnConflicts;

	private List<ObserverOnSolving> collectObserversOnSolving() {
		Stream<Object> stream = Stream.concat(Stream.of(problem.constraints), Stream.of(head.output, stats)).filter(c -> c instanceof ObserverOnSolving);
		return stream.map(o -> (ObserverOnSolving) o).collect(toCollection(ArrayList::new));
	}

	private List<ObserverOnRuns> collectObserversOnRuns() {
		List<ObserverOnRuns> list = new ArrayList<>();
		if (head.control.solving.enableSearch) {
			if (nogoodRecorder != null && nogoodRecorder.symmetryHandler != null)
				list.add(nogoodRecorder.symmetryHandler);
			Stream.of(this, restarter, ipsRecorder, heuristic, lastConflict, stats).filter(o -> o instanceof ObserverOnRuns)
					.forEach(o -> list.add((ObserverOnRuns) o));
		}
		Stream.of(problem.constraints).filter(c -> c instanceof ObserverOnRuns).forEach(c -> list.add((ObserverOnRuns) c));
		if (propagation instanceof ObserverOnRuns)
			list.add((ObserverOnRuns) propagation);
		list.add(head.output);
		return list;
	}

	private List<ObserverOnBacktracksSystematic> collectObserversOnBacktracksSystematic() {
		// keep 'this' at first position in the list
		Stream<Object> stream = Stream.concat(Stream.of(this, propagation), Stream.of(problem.constraints))
				.filter(c -> c instanceof ObserverOnBacktracksSystematic);
		return stream.map(o -> (ObserverOnBacktracksSystematic) o).collect(toCollection(ArrayList::new));
	}

	private List<ObserverOnDecisions> collectObserversOnDecisions() {
		Stream<Object> stream = Stream.of(this, tracer, stats, lastConflict, proofer).filter(o -> o instanceof ObserverOnDecisions);
		return stream.map(o -> (ObserverOnDecisions) o).collect(toCollection(ArrayList::new));
	}

	private List<ObserverOnAssignments> collectObserversOnAssignments() {
		return Stream.of(heuristic).filter(o -> o instanceof ObserverOnAssignments).map(o -> (ObserverOnAssignments) o).collect(toCollection(ArrayList::new));
	}

	private List<ObserverOnConflicts> collectObserversOnConflicts() {
		return Stream.of(heuristic).filter(o -> o instanceof ObserverOnConflicts).map(o -> (ObserverOnConflicts) o).collect(toCollection(ArrayList::new));
	}

	/**********************************************************************************************
	 * Fields and Constructor
	 *********************************************************************************************/

	/**
	 * The main object, leading (head of) resolution
	 */
	public final Head head;

	/**
	 * The problem to be solved
	 */
	public final Problem problem;

	/**
	 * The object used for constraint propagation
	 */
	public Propagation propagation;
	/**
	 * The object that implements the restarting policy of the solver
	 */
	public final Restarter restarter;

	/**
	 * The variable ordering heuristic used to select variables
	 */
	public HeuristicVariables heuristic;

	/**
	 * The object implementing last-conflict reasoning (may be null)
	 */
	public final LastConflict lastConflict; // reasoner about last conflicts (lc)

	/**
	 * The object handling/storing the decisions taken by the solver
	 */
	public final Decisions decisions;

	/**
	 * The object handling/storing the solutions found by the solver
	 */
	public final Solutions solutions;

	/**
	 * The object managing past and future variables, i.e., the variables that are, and are not, explicitly assigned by the solver
	 */
	public final FutureVariables futVars;

	public final StackedVariables stackedVariables;

	public final NogoodRecorder nogoodRecorder;

	public final IpsRecorder ipsRecorder;

	public final Proofer proofer;

	public final SetSparseReversible entailed; // the number (field num) of entailed constraints

	public final RunProgressSaver runProgressSaver;

	public final WarmStarter warmStarter;

	public int minDepth, maxDepth;

	public NogoodMinimizer nogoodMinimizer;

	/**
	 * when null, the solver is still running
	 */
	public Stopping stopping;

	public final Tracer tracer;

	/**
	 * The statistics of the solver
	 */
	public Statistics stats;

	private final Variable[] lastPastBeforeRun = new Variable[2];

	private int nRecursiveRuns = 0;

	public final boolean isFullExploration() {
		return stopping == FULL_EXPLORATION;
	}

	public final boolean finished() {
		if (stopping != null)
			return true;
		if (head.isTimeExpiredForCurrentInstance()) {
			stopping = EXCEEDED_TIME;
			return true;
		}
		return false;
	}

	public final void resetNoSolutions() {
		stopping = null;
		solutions.found = 0;
	}

	public void reset() { // called by very special objects (for example, when extracting a MUC)
		control(futVars.nPast() == 0);
		propagation.reset();
		restarter.reset();
		resetNoSolutions();
		decisions.reset();
		heuristic.setPriorityVars(problem.priorityVars, 0);
		// lastConflict.beforeRun();
		if (nogoodRecorder != null)
			nogoodRecorder.reset();
		control(ipsRecorder == null);
		control(stackedVariables.top == -1, () -> "Top= " + stackedVariables.top);
		this.stats = new Statistics(this); // for simplicity, stats are rebuilt
		control(proofer == null);
	}

	public Solver(Head head) {
		this.head = head;
		this.problem = head.problem;
		this.problem.solver = this;

		this.solutions = new Solutions(this, head.control.general.nSearchedSolutions); // BE CAREFUL: build solutions before propagation
		this.propagation = Propagation.buildFor(this); // may be null
		if (!head.control.propagation.useAuxiliaryQueues)
			Stream.of(problem.constraints).forEach(c -> c.filteringComplexity = 0);
		this.restarter = Restarter.buildFor(this);

		this.heuristic = HeuristicVariables.buildFor(this);
		for (Variable x : problem.variables)
			x.heuristic = HeuristicValues.buildFor(x); // buildValueOrderingHeuristic();
		this.lastConflict = head.control.varh.lc > 0 ? new LastConflict(this, head.control.varh.lc) : null;
		this.decisions = new Decisions(this);

		this.futVars = new FutureVariables(this);
		int nLevels = problem.variables.length + 1;
		int size = Stream.of(problem.variables).mapToInt(x -> x.dom.initSize()).reduce(0, (sum, domSize) -> sum + Math.min(nLevels, domSize));
		this.stackedVariables = new StackedVariables(size + nLevels);

		this.nogoodRecorder = NogoodRecorder.buildFor(this); // may be null
		this.ipsRecorder = IpsRecorder.buildFor(this); // may be null
		this.proofer = ipsRecorder != null && ipsRecorder.reductionOperator.enablePElimination() ? new Proofer() : null;

		this.entailed = new SetSparseReversible(problem.constraints.length, nLevels, false);

		this.observersOnSolving = collectObserversOnSolving();
		this.observersOnRuns = collectObserversOnRuns();
		this.observersOnBacktracksSystematic = collectObserversOnBacktracksSystematic();
		this.observersOnDecisions = collectObserversOnDecisions();
		this.observersOnAssignments = collectObserversOnAssignments();
		this.observersOnConflicts = collectObserversOnConflicts();

		this.runProgressSaver = head.control.valh.runProgressSaving ? new RunProgressSaver() : null;
		this.warmStarter = head.control.valh.warmStart.length() > 0 ? new WarmStarter(head.control.valh.warmStart) : null;

		this.tracer = head.control.general.trace.length() != 0 ? new Tracer(head.control.general.trace) : null;
		this.stats = new Statistics(this);

		this.nogoodMinimizer = new NogoodMinimizer(this);
	}

	public int depth() {
		return futVars.nPast();
	}

	public void entail(Constraint c) {
		// System.out.println("entailed at " + depth() + " " + c);
		entailed.add(c.num, depth());
	}

	public boolean isEntailed(Constraint c) {
		return entailed.contains(c.num);
	}

	/**
	 * Records the variable among those (whose domain is) modified at the current level (depth)
	 * 
	 * @param x
	 *            a variable
	 * @return the level at which the variable is stacked
	 */
	public int stackVariable(Variable x) {
		return stackedVariables.push(x);
	}

	public void assign(Variable x, int a) {
		assert !x.assigned();

		stats.nAssignments++;
		futVars.remove(x);
		x.assign(a);
		decisions.addPositiveDecision(x, a);
		for (ObserverOnAssignments obs : observersOnAssignments)
			obs.afterAssignment(x, a);
	}

	public final void backtrack(Variable x) { // should we call it unassign or retract instead?
		// System.out.println("back " + x + x.dom.uniqueValue());
		int depthBeforeBacktrack = depth();
		futVars.add(x);
		x.unassign();
		decisions.delPositiveDecision(x);
		for (ObserverOnAssignments obs : observersOnAssignments)
			obs.afterUnassignment(x);
		for (ObserverOnBacktracksSystematic obs : observersOnBacktracksSystematic)
			obs.restoreBefore(depthBeforeBacktrack);
		if (propagation instanceof Forward)
			propagation.queue.clear();
	}

	public final void backtrack() {
		backtrack(futVars.lastPast());
	}

	public final boolean tryAssignment(Variable x, int a) {
		boolean b = false; // TODO temporary
		if (b && x.heuristic instanceof Bivs) {
			SetDense inconsistent = ((Bivs) x.heuristic).inconsistent;
			if (inconsistent.size() > 0) {
				boolean inc = inconsistent.size() == x.dom.size();
				if (!inc) {
					boolean r = x.dom.remove(inconsistent);
					assert r;
					inc = propagation.propagate() == false;
				}
				inconsistent.clear();
				if (inc) {
					stats.nWrongDecisions++; // necessary for updating restart data
					stats.nFailedAssignments++;
					return false;
				}
			}
		}
		for (ObserverOnDecisions observer : observersOnDecisions)
			observer.beforePositiveDecision(x, a);
		assign(x, a);
		boolean consistent = propagation.runAfterAssignment(x) && (ipsRecorder == null || ipsRecorder.dealWhenOpeningNode());
		if (!consistent) {
			x.failed[a]++;
			stats.nWrongDecisions++;
			stats.nFailedAssignments++;
			// if (ngdRecorder != null) ngdRecorder.addCurrentNogood();
			return false;
		}
		// if (ipsRecorder != null && !ipsRecorder.dealWhenOpeningNode()) return false;
		return true;
	}

	public final boolean tryAssignment(Variable x) {
		return tryAssignment(x, x.heuristic.bestIndex());
	}

	/**
	 * Called when an empty domain has been encountered.
	 */
	protected void manageEmptyDomainBeforeBacktracking() {
		if (runProgressSaver != null)
			runProgressSaver.manageEmptyDomainBeforeBacktracking();

		if (tracer != null)
			tracer.onBacktrack();
		stats.nBacktracks++;
		if (ipsRecorder != null)
			ipsRecorder.dealWhenClosingNode();
		if (futVars.nPast() == 0)
			stopping = Stopping.FULL_EXPLORATION;
	}

	protected final boolean tryRefutation(Variable x, int a) {
		if (x.dom instanceof DomainInfinite)
			return false;

		for (ObserverOnDecisions observer : observersOnDecisions)
			observer.beforeNegativeDecision(x, a);
		decisions.addNegativeDecision(x, a);
		x.dom.removeElementary(a);
		boolean consistent = x.dom.size() > 0;
		if (consistent) {
			if (head.control.solving.branching == Branching.NON)
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
	private void manageContradiction(ConstraintGlobal objectiveToCheck) {
		for (boolean consistent = false; !consistent && stopping != Stopping.FULL_EXPLORATION;) {
			Variable x = futVars.lastPast();
			if (x == lastPastBeforeRun[nRecursiveRuns - 1] && !head.control.lns.enabled)
				stopping = Stopping.FULL_EXPLORATION;
			else {
				int a = x.dom.single();
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
				if (tryAssignment(heuristic.bestVar()) == false)
					manageContradiction(null);
			}
			if (futVars.size() == 0) {
				solutions.handleNewSolution();
				boolean copContinue = problem.settings.framework == COP && !head.control.restarts.restartAfterSolution;
				ConstraintGlobal objectiveCtr = copContinue ? (ConstraintGlobal) problem.optimizer.ctr : null;
				if (copContinue) {
					// first, we directly change the limit value of the leading objective constraint
					problem.optimizer.ctr.limit(problem.optimizer.ctr.objectiveValue() + (problem.optimizer.minimization ? -1 : 1));
					// next, we backtrack to the level where a value for a variable in the scope of the objective was removed for the last time
					int backtrackLevel = -1;
					for (int i = 0; i < objectiveCtr.scp.length; i++) {
						Variable x = objectiveCtr.scp[objectiveCtr.futvars.dense[i]]; // variables (of the objective) from the last to the first assigned
						if (x.assignmentLevel <= backtrackLevel)
							break;
						backtrackLevel = Math.max(backtrackLevel, x.dom.lastRemovedLevel());
					}
					assert backtrackLevel != -1;
					while (depth() > backtrackLevel)
						backtrack(futVars.lastPast());
					// check with java -ea ac /home/lecoutre/workspace/AbsCon/build/resources/main/cop/Photo.xml.lzma -ev
					// java -ea ac /home/lecoutre/workspace/AbsCon/build/resources/main/cop/Recipe.xml.lzma
				}
				if (problem.settings.framework == COP) // && isEntailed(objectiveCtr)) TODO why is-it incorrect to use the second part of the test?
					entailed.clear();
				if (!finished() && !restarter.currRunFinished())
					manageContradiction(objectiveCtr);
			}
		}
		minDepth = decisions.minDepth(); // need to be recorded before backtracking to the root
		if (nogoodRecorder != null && !finished() && !restarter.allRunsFinished())
			nogoodRecorder.addNogoodsOfCurrentBranch();
	}

	private void backtrackTo(Variable x) {
		if (x != null && !x.assigned()) // TODO LNS does not necessarily respect the last past recorded variable
			x = null;
		// assert x == null || x.isAssigned();
		while (futVars.lastPast() != x)
			backtrack(futVars.lastPast());
	}

	public final void backtrackToTheRoot() {
		backtrackTo(null);
	}

	private final void doPrepro() {
		for (ObserverOnSolving observer : observersOnSolving)
			observer.beforePreprocessing();
		if (propagation.runInitially() == false)
			stopping = FULL_EXPLORATION;
		for (ObserverOnSolving observer : observersOnSolving)
			observer.afterPreprocessing();
	}

	public Solver doRun() {
		lastPastBeforeRun[nRecursiveRuns++] = futVars.lastPast();
		explore();
		backtrackTo(lastPastBeforeRun[--nRecursiveRuns]);
		return this;
	}

	protected final void doSearch() {
		for (ObserverOnSolving observer : observersOnSolving)
			observer.beforeSearch();
		while (!finished() && !restarter.allRunsFinished()) {
			for (ObserverOnRuns observer : observersOnRuns)
				observer.beforeRun();
			if (stopping != FULL_EXPLORATION) // an observer might modify the object stopping
				doRun();
			for (ObserverOnRuns observer : observersOnRuns)
				observer.afterRun();
			decisions.reset(); // TODO put in an observer ?
		}
		for (ObserverOnSolving observer : observersOnSolving)
			observer.afterSearch();
	}

	/**
	 * This method allows to solve the attached problem instance.
	 */
	public void solve() {
		for (ObserverOnSolving observer : observersOnSolving)
			observer.beforeSolving();
		if (Variable.firstWipeoutVariableIn(problem.variables) != null)
			stopping = FULL_EXPLORATION; // because some search observers may detect an inconsistency
		if (!finished() && head.control.solving.enablePrepro)
			doPrepro();
		if (!finished() && head.control.solving.enableSearch)
			doSearch();
		for (ObserverOnSolving observer : observersOnSolving)
			observer.afterSolving();
		restoreProblem();
	}

	/**
	 * Called in order to get the problem back in its initial state.
	 */
	public final void restoreProblem() {
		backtrackToTheRoot();
		// we also undo preprocessing propagation
		stackedVariables.restoreBefore(0);
		observersOnBacktracksSystematic.stream().forEach(obs -> obs.restoreBefore(0));
		assert decisions.set.size() == 0; // decisions.reset();
		// nPurged not updated; see java -ea abscon.Resolution problems.patt.QuasiGroup -data=6 -model=v5 -ev -cm=false
		assert Stream.of(problem.variables).allMatch(x -> x.dom.controlStructures());
	}
}

// boolean b = restarter.numRun % diviser == 0;
// if (restarter.numRun % 20 == 0)
// diviser++;
// // if (b) {
// Domain.setMarks(pb.variables);
// if (solManager.found > 0) {
// SumSimpleLE c = (SumSimpleLE) pb.optimizer.ctr;
// Variable x = c.mostImpacting();
// int v = x.dom.toVal(solManager.lastSolution[x.num]);
// x.dom.removeValuesGE(v);
// System.out.println("ccccc most " + x + " " + x.dom.toVal(solManager.lastSolution[x.num]));
// }
// }

// if (b)
// Domain.restoreAtMarks(pb.variables);
