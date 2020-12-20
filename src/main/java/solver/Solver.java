/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package solver;

import static org.xcsp.common.Types.TypeFramework.COP;
import static utility.Enums.EStopping.EXCEEDED_TIME;
import static utility.Enums.EStopping.FULL_EXPLORATION;
import static utility.Kit.log;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.StringTokenizer;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;

import constraints.Constraint;
import constraints.Constraint.CtrGlobal;
import heuristics.HeuristicValuesDynamic.Bivs;
import heuristics.HeuristicValuesDynamic.Failures;
import heuristics.HeuristicVariables;
import interfaces.Observers.ObserverAssignment;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Observers.ObserverConflicts;
import interfaces.Observers.ObserverRuns;
import interfaces.Observers.ObserverSearch;
import learning.IpsRecorder;
import learning.NogoodMinimizer;
import learning.NogoodRecorder;
import main.Head;
import problem.Problem;
import propagation.Forward;
import propagation.Propagation;
import sets.SetDense;
import sets.SetSparseReversible;
import solver.Statistics.StatisticsBacktrack;
import utility.Enums.EBranching;
import utility.Enums.EStopping;
import utility.Kit;
import variables.DomainInfinite;
import variables.Variable;

public class Solver implements ObserverRuns, ObserverBacktrackingSystematic {

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
					int a = problem.variables[i].dom.toPresentIdx(Integer.parseInt(t[i]));
					Kit.control(a != -1);
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
			return solRecorder.found > 0 && head.control.valh.solutionSaving;
		}

		void manageEmptyDomainBeforeBacktracking() {
			if (desactivated())
				return;
			int d = depth(); // or Variable.nSingletonVariablesIn(pb.variables) ??
			if (d >= currSize) {
				currSize = d;
				for (int i = 0; i < prevLongestRunBranch.length; i++)
					prevLongestRunBranch[i] = problem.variables[i].dom.size() == 1 ? problem.variables[i].dom.unique() : -1;
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
			assert stack[top] instanceof Variable;
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

	public final class Proofer {
		private final boolean active;

		public final boolean[][] proofVariables;

		public Proofer(IpsRecorder recorder) {
			this.active = recorder != null && ipsRecorder.reductionOperator.enablePElimination();
			this.proofVariables = this.active ? new boolean[problem.variables.length + 1][problem.variables.length] : null;
		}

		public void updateProof(Constraint c) {
			if (active)
				for (Variable x : c.scp)
					proofVariables[depth()][x.num] = true;
		}

		public void updateProof(int[] nums) {
			if (active)
				for (int num : nums)
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
				for (int i = problem.variables.length - 1; i >= 0; i--)
					if (proofVariables[d + 1][i])
						proofVariables[d][i] = true;
			}
		}
	}

	/**********************************************************************************************
	 * Intern class Tracer
	 *********************************************************************************************/

	public final class Tracer {
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

	public final List<ObserverSearch> observersSearch;

	public List<ObserverRuns> observersRuns;

	public List<ObserverAssignment> observersAssignment;

	public List<ObserverConflicts> observersConflicts;

	public int stackVariable(Variable x) {
		return stackedVariables.push(x);
	}

	private List<ObserverBacktrackingSystematic> collectObserversBacktrackingSystematic() {
		List<ObserverBacktrackingSystematic> list = new ArrayList<>();
		list.add(this); // because must be at first position in the list
		Stream.of(problem.constraints).filter(c -> c instanceof ObserverBacktrackingSystematic).forEach(c -> list.add((ObserverBacktrackingSystematic) c));
		if (propagation instanceof ObserverBacktrackingSystematic)
			list.add((ObserverBacktrackingSystematic) propagation);
		return list;
	}

	protected List<ObserverRuns> collectObserversRuns() {
		List<ObserverRuns> list = new ArrayList<>();
		if (head.control.solving.enableSearch) {
			if (nogoodRecorder != null && nogoodRecorder.symmetryHandler != null)
				list.add((ObserverRuns) nogoodRecorder.symmetryHandler);
			Stream.of(this, restarter, ipsRecorder, heuristic, lastConflict, stats).filter(o -> o instanceof ObserverRuns)
					.forEach(o -> list.add((ObserverRuns) o));
		}
		Stream.of(problem.constraints).filter(c -> c instanceof ObserverRuns).forEach(c -> list.add((ObserverRuns) c));
		if (propagation instanceof ObserverRuns)
			list.add((ObserverRuns) propagation);
		list.add(head.output);
		return list;
	}

	protected List<ObserverAssignment> collectObserversAssignment() {
		List<ObserverAssignment> list = new ArrayList<>();
		if (heuristic instanceof ObserverAssignment)
			list.add((ObserverAssignment) heuristic);
		return list;
	}

	protected List<ObserverConflicts> collectObserversPropagation() {
		List<ObserverConflicts> list = new ArrayList<>();
		if (heuristic instanceof ObserverConflicts)
			list.add((ObserverConflicts) heuristic);
		return list;
	}

	/**********************************************************************************************
	 * Fields and Constructor
	 *********************************************************************************************/

	/**
	 * The main object, head of resolution
	 */
	public final Head head;

	/**
	 * The problem to be solved
	 */
	public final Problem problem;

	public final FutureVariables futVars;

	public final SolutionRecorder solRecorder;

	/**
	 * The object that implements the restarts policy of the solver.
	 */
	public final Restarter restarter;

	public Propagation propagation;

	public final DecisionRecorder decRecorder;

	public HeuristicVariables heuristic;

	public final LastConflict lastConflict; // reasoner about last conflicts (lc)

	public final NogoodRecorder nogoodRecorder;

	public final IpsRecorder ipsRecorder;

	public final Proofer proofer;

	public final StackedVariables stackedVariables;

	public final SetSparseReversible entailed; // the number (field num) of entailed constraints

	public final List<ObserverBacktrackingSystematic> observersBacktrackingSystematic;

	public final RunProgressSaver runProgressSaver;

	public final WarmStarter warmStarter;

	public final Tracer tracer;

	public int minDepth, maxDepth;

	public NogoodMinimizer nogoodMinimizer;

	/**
	 * when null, the solver is still running
	 */
	public EStopping stopping;

	public Statistics stats;

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
		solRecorder.found = 0;
	}

	public void reset() { // called by very special objects (for example, when extracting a MUC)
		Kit.control(futVars.nDiscarded() == 0);
		// Kit.control(!(propagation instanceof TagBinaryRelationFiltering), () -> "for the moment");
		propagation.reset();
		restarter.reset();
		resetNoSolutions();

		decRecorder.reset();
		// if (!(heuristicVars instanceof HeuristicVariablesConflictBased) || !preserveWeightedDegrees)
		// heuristicVars.reset();
		heuristic.setPriorityVars(problem.priorityVars, 0);
		lastConflict.beforeRun();
		if (nogoodRecorder != null)
			nogoodRecorder.reset();
		Kit.control(ipsRecorder == null);
		Kit.control(stackedVariables.top == -1, () -> "Top= " + stackedVariables.top);
		stats = new StatisticsBacktrack(this);
		Kit.control(!proofer.active);
	}

	public Solver(Head head) {
		this.head = head;
		this.problem = head.problem;
		this.problem.solver = (Solver) this;
		this.futVars = new FutureVariables(problem.variables);
		this.solRecorder = new SolutionRecorder(this, head.control.general.nSearchedSolutions); // build solutionManager before propagation
		this.propagation = Propagation.buildFor(this); // may be null
		if (!head.control.propagation.useAuxiliaryQueues)
			Stream.of(problem.constraints).forEach(c -> c.filteringComplexity = 0);
		this.restarter = Restarter.buildFor(this);
		this.observersSearch = Stream.of(problem.constraints).filter(c -> c instanceof ObserverSearch).map(c -> (ObserverSearch) c)
				.collect(Collectors.toCollection(ArrayList::new));
		observersSearch.add(head.output);

		this.decRecorder = new DecisionRecorder(this);
		this.heuristic = HeuristicVariables.buildFor(this);
		for (Variable x : problem.variables)
			x.buildValueOrderingHeuristic();
		this.lastConflict = new LastConflict(this, head.control.varh.lc);
		this.nogoodRecorder = NogoodRecorder.buildFor(this); // may be null
		this.ipsRecorder = IpsRecorder.buildFor(this); // may be null
		this.proofer = new Proofer(ipsRecorder);

		int nLevels = problem.variables.length + 1;
		int size = Stream.of(problem.variables).mapToInt(x -> x.dom.initSize()).reduce(0, (sum, domSize) -> sum + Math.min(nLevels, domSize));
		this.stackedVariables = new StackedVariables(size + nLevels);
		this.entailed = new SetSparseReversible(problem.constraints.length, false, nLevels);
		this.observersBacktrackingSystematic = collectObserversBacktrackingSystematic();
		this.observersRuns = collectObserversRuns();
		this.observersAssignment = collectObserversAssignment();
		this.observersConflicts = collectObserversPropagation();

		this.tracer = new Tracer(head.control.general.trace);
		this.stats = new StatisticsBacktrack(this);
		observersSearch.add(0, this.stats); // this list is initialized in the super-class

		this.runProgressSaver = head.control.valh.runProgressSaving ? new RunProgressSaver() : null;
		this.warmStarter = head.control.valh.warmStart.length() > 0 ? new WarmStarter(head.control.valh.warmStart) : null;

		this.nogoodMinimizer = new NogoodMinimizer(this);
	}

	public int depth() {
		return futVars.nDiscarded();
	}

	public void entail(Constraint c) {
		// System.out.println("entailed at " + depth() + " " + c);
		entailed.add(c.num, depth());
	}

	public boolean isEntailed(Constraint c) {
		return entailed.isPresent(c.num);
	}

	public void assign(Variable x, int a) {
		assert !x.assigned();

		stats.nAssignments++;
		futVars.assign(x);
		x.doAssignment(a);
		decRecorder.addPositiveDecision(x, a);
		for (ObserverAssignment obs : observersAssignment)
			obs.afterAssignment(x, a);
	}

	public final void backtrack(Variable x) { // should we call it unassign or retract instead?
		int depthBeforeBacktrack = depth();
		futVars.unassign(x);
		x.undoAssignment();
		decRecorder.delPositiveDecision(x);
		for (ObserverAssignment obs : observersAssignment)
			obs.afterUnassignment(x);
		for (ObserverBacktrackingSystematic obs : observersBacktrackingSystematic)
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
		tracer.onAssignment(x, a);
		stats.onAssignment(x);
		lastConflict.onAssignment(x);
		assign(x, a);
		proofer.reset();
		boolean consistent = propagation.runAfterAssignment(x) && (ipsRecorder == null || ipsRecorder.dealWhenOpeningNode());
		if (x.heuristic instanceof Failures)
			((Failures) x.heuristic).updateWith(a, depth(), consistent);
		if (!consistent) {
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

		tracer.onBacktrack();
		stats.nBacktracks++;
		if (ipsRecorder != null)
			ipsRecorder.dealWhenClosingNode();
		if (futVars.nDiscarded() == 0)
			stopping = EStopping.FULL_EXPLORATION;
	}

	protected final boolean tryRefutation(Variable x, int a) {
		if (x.dom instanceof DomainInfinite)
			return false;
		tracer.onRefutation(x, a);
		stats.onRefutation(x);
		lastConflict.onRefutation(x, a);
		decRecorder.addNegativeDecision(x, a);
		proofer.recopy();
		x.dom.removeElementary(a);
		boolean consistent = x.dom.size() > 0;
		if (consistent) {
			if (head.control.solving.branching == EBranching.NON)
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
		for (boolean consistent = false; !consistent && stopping != EStopping.FULL_EXPLORATION;) {
			Variable x = futVars.lastPast();
			if (x == lastPastBeforeRun[nRecursiveRuns - 1] && !head.control.lns.enabled)
				stopping = EStopping.FULL_EXPLORATION;
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
				if (tryAssignment(heuristic.bestVar()) == false)
					manageContradiction(null);
			}
			if (futVars.size() == 0) {
				solRecorder.handleNewSolution();
				boolean copContinue = problem.settings.framework == COP && !head.control.restarts.restartAfterSolution;
				CtrGlobal objectiveCtr = copContinue ? (CtrGlobal) problem.optimizer.ctr : null;
				if (copContinue) {
					// first, we directly change the limit value of the leading objective constraint
					problem.optimizer.ctr.limit(problem.optimizer.ctr.objectiveValue() + (problem.optimizer.minimization ? -1 : 1));
					// next, we backtrack to the level where a value for a variable in the scope of the objective was removed for the last time
					int backtrackLevel = -1;
					for (int i = 0; i < objectiveCtr.scp.length; i++) {
						Variable x = objectiveCtr.scp[objectiveCtr.futvars.dense[i]]; // variables (of the objective) from the last to the first assigned
						if (x.assignmentLevel() <= backtrackLevel)
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
		minDepth = decRecorder.minDepth(); // need to be recorded before backtracking to the root
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

	public void backtrackToTheRoot() {
		backtrackTo(null);
	}

	public Solver doRun() {
		lastPastBeforeRun[nRecursiveRuns++] = futVars.lastPast();
		explore();
		backtrackTo(lastPastBeforeRun[--nRecursiveRuns]);
		return this;
	}

	private final Variable[] lastPastBeforeRun = new Variable[2];

	private int nRecursiveRuns = 0;

	private final void doPrepro() {
		for (ObserverSearch observer : observersSearch)
			observer.beforePreprocessing();
		if (propagation.runInitially() == false)
			stopping = FULL_EXPLORATION;
		for (ObserverSearch observer : observersSearch)
			observer.afterPreprocessing();
	}

	protected final void doSearch() {
		for (ObserverSearch observer : observersSearch)
			observer.beforeSearch();
		while (!finished() && !restarter.allRunsFinished()) {
			for (ObserverRuns observer : observersRuns)
				observer.beforeRun();

			// boolean b = restarter.numRun % diviser == 0;
			// if (restarter.numRun % 20 == 0)
			// diviser++;
			// System.out.println("bbbb " + b);
			// if (b) {
			// Domain.setMarks(pb.variables);
			// if (solManager.found > 0) {
			// SumSimpleLE c = (SumSimpleLE) pb.optimizer.ctr;
			// Variable x = c.mostImpacting();
			// int v = x.dom.toVal(solManager.lastSolution[x.num]);
			// x.dom.removeValuesGE(v);
			// System.out.println("ccccc most " + x + " " + x.dom.toVal(solManager.lastSolution[x.num]));
			// }
			// }

			if (stopping != FULL_EXPLORATION) // an observer might modify the object stoppingType
				doRun();

			// if (b)
			// Domain.restoreAtMarks(pb.variables);

			for (ObserverRuns observer : observersRuns)
				observer.afterRun();
		}
		for (ObserverSearch observer : observersSearch)
			observer.afterSearch();
	}

	/**
	 * This method allows to solve the attached problem instance.
	 */
	public void solve() {
		for (ObserverSearch observer : observersSearch)
			observer.beforeSolving();
		if (Variable.firstWipeoutVariableIn(problem.variables) != null)
			stopping = FULL_EXPLORATION;
		if (!finished() && head.control.solving.enablePrepro)
			doPrepro();
		if (!finished() && head.control.solving.enableSearch)
			doSearch();
		for (ObserverSearch observer : observersSearch)
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
		observersBacktrackingSystematic.stream().forEach(obs -> obs.restoreBefore(0));
		decRecorder.reset();
		// nPurged not updated; see java -ea abscon.Resolution problems.patt.QuasiGroup -data=6 -model=v5 -ev -cm=false
		assert Stream.of(problem.variables).allMatch(x -> x.dom.controlStructures());
	}
}
