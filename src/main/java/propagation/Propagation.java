/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import java.util.HashSet;
import java.util.Set;

import constraints.Constraint;
import constraints.ConstraintGlobal;
import dashboard.Control.OptionsPropagation;
import heuristics.HeuristicVariablesDynamic.PickOnDom;
import heuristics.HeuristicVariablesDynamic.ProcOnDom;
import heuristics.HeuristicVariablesDynamic.RunRobin;
import interfaces.Observers.ObserverOnConflicts;
import learning.IpsReasonerDominance;
import sets.SetSparse;
import sets.SetSparse.SetSparseCnt;
import solver.Solver;
import solver.Solver.Stopping;
import utility.Reflector;
import variables.Domain;
import variables.Variable;

/**
 * The is the root class for any object used to manage constraint propagation. For simplicity, propagation and consistency concepts are not distinguished. So,
 * some subclasses are given the name of consistencies.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Propagation {

	/*************************************************************************
	 * Static members
	 *************************************************************************/

	private static final int MAX_FILTERING_COMPLEXITY = 2;

	/**
	 * Builds and returns the propagation to be attached to the specified solver. If preprocessing and search stages are disabled, null is returned.
	 * 
	 * @param solver
	 *            the solver to which the propagation object is attached
	 * @return the propagation to be attached to the specified solver (possibly, null)
	 */
	public static Propagation buildFor(Solver solver) {
		if (!solver.head.control.solving.enablePrepro && !solver.head.control.solving.enableSearch)
			return null;
		return Reflector.buildObject(solver.head.control.propagation.clazz, solver.head.availableClasses.get(Propagation.class), solver);
	}

	/*************************************************************************
	 * Inner classes for managing auxiliary queues and reasoning with nogoods
	 *************************************************************************/

	static final class SetSparseMap extends SetSparse {

		/**
		 * Values associated with elements (indexes) currently stored in the set
		 */
		public final int[] values;

		public SetSparseMap(int capacity) {
			super(capacity, false);
			this.values = new int[capacity];
		}

		@Override
		public final boolean add(int a) {
			throw new RuntimeException("Must not be called without a second argument");
		}

		/**
		 * Ass the specified element, while recording an associated value
		 * 
		 * @param a
		 *            an element (typically, index of value)
		 * @param value
		 * @return true if the element has been added
		 */
		public boolean add(int a, int value) {
			boolean b = super.add(a);
			values[a] = value; // even if a is already present, the new value is recorded
			return b;
		}
	}

	private final class NogoodReasoning {

		private Boolean ipsDominanceReasoning;

		private int[] absentValuesSentinel;

		private long[] sentinelLevel;

		public boolean isNogoodConsistent(Variable x) {
			Domain dom = x.dom;
			if (solver.nogoodReasoner != null)
				if (dom.size() == 1 && solver.nogoodReasoner.checkWatchesOf(x, dom.first(), false) == false)
					return false;
			if (ipsDominanceReasoning == null) { // first call
				ipsDominanceReasoning = solver.ipsReasoner instanceof IpsReasonerDominance ? Boolean.TRUE : Boolean.FALSE;
				if (ipsDominanceReasoning) {
					this.absentValuesSentinel = new int[solver.problem.variables.length];
					this.sentinelLevel = new long[solver.problem.variables.length];
				}
			}
			if (ipsDominanceReasoning) {
				IpsReasonerDominance ipsReasoner = (IpsReasonerDominance) solver.ipsReasoner;
				if (sentinelLevel[x.num] != solver.stats.safeNumber())
					absentValuesSentinel[x.num] = -1;
				int depth = solver.depth();
				int lastRemoved = dom.lastRemoved();
				for (int a = lastRemoved; a != absentValuesSentinel[x.num] && dom.removedLevelOf(a) == depth; a = dom.prevRemoved(a))
					if (!ipsReasoner.checkWatchesOf(x, a))
						return false;
				sentinelLevel[x.num] = solver.stats.safeNumber();
				absentValuesSentinel[x.num] = lastRemoved;
			}
			return true;
		}
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/**
	 * The solver to which the propagation object is attached.
	 */
	public final Solver solver;

	/**
	 * The queue (actually, set) used to contain variables during propagation.
	 */
	public final Queue queue;

	/**
	 * Auxiliary queues for handling constraints with different levels of propagator complexities. Currently, its usage is experimental.
	 */
	// public final SetSparseMap[] auxiliaryQueues;

	public final Set<Constraint> postponedConstraints;

	/**
	 * This field is used as a clock to enumerate time. It is used to avoid performing some useless calls of constraint propagators by comparing time-stamps
	 * attached to variables with time-stamps attached to constraints.
	 * 
	 */
	public long time;

	/**
	 * The constraint that is currently used in propagation. This is null if no constraint is currently used for filtering. This is relevant for AC.
	 */
	public Constraint currFilteringCtr;

	/**
	 * The variable that has been wiped out the last time constraint propagation led to failure
	 */
	public Variable lastWipeoutVar;

	/**
	 * The object to be used when picking a variable from the queue in order to reason first with recorded nogoods (if any)
	 */
	private NogoodReasoning nogoodReasoning = new NogoodReasoning();

	/**
	 * When true, indicates that the object is currently performing a form of search during propagation. This may be the case for some forms of propagation
	 * based on strong consistencies.
	 */
	public boolean performingProperSearch;

	/**
	 * Metrics for filtering approaches (e.g., SAC) based on singleton tests. Put in the root class for simplicity.
	 */
	public long nSingletonTests, nEffectiveSingletonTests;

	/**
	 * The accumulated number of tuples removed by propagation (meaningful for some strong consistencies)
	 */
	public int nTuplesRemoved;

	/**
	 * The options concerning propagation
	 */
	protected final OptionsPropagation options;

	/**
	 * This field is set to true when running propagation from scratch at the root node must be made when a restart occurs.
	 */
	public boolean runAtNextRoot;

	public SetSparseCnt historyX;

	public SetSparseCnt historyC;

	/*************************************************************************
	 * Methods
	 *************************************************************************/

	public void clear() {
		queue.clear();
		postponedConstraints.clear();
	}

	/**
	 * Increments the value of the clock (time counter), and returns it.
	 * 
	 * @return the incremented time of the clock
	 */
	public final long incrementTime() {
		return ++time;
	}

	/**
	 * Builds a propagation object to be attached to the specified solver
	 * 
	 * @param solver
	 *            the solver to which the propagation object is attached
	 */
	public Propagation(Solver solver) {
		this.solver = solver;
		this.queue = this instanceof Forward ? new Queue((Forward) this) : null;
		this.options = solver.head.control.propagation;
		// int nAuxQueues = options.useAuxiliaryQueues ? MAX_FILTERING_COMPLEXITY : 0;
		// this.auxiliaryQueues = this instanceof Forward
		// ? IntStream.range(0, nAuxQueues).mapToObj(i -> new
		// SetSparseMap(solver.problem.constraints.length)).toArray(SetSparseMap[]::new)
		// : null;
		this.postponedConstraints = new HashSet<>();
		String clazz = solver.head.control.varh.clazz;
		this.historyX = clazz.equals(PickOnDom.class.getSimpleName()) || clazz.equals(RunRobin.class.getSimpleName())
				? new SetSparseCnt(solver.problem.variables.length)
				: null;
		this.historyC = clazz.equals(ProcOnDom.class.getSimpleName()) ? new SetSparseCnt(solver.problem.constraints.length) : null;

	}

	/**
	 * Pick and delete a variable from the queue and call filtering algorithms associated with the constraints involving the variable. Possibly postpone
	 * filtering if auxiliary queues are used.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean pickAndFilter() {
		boolean consistent = true;
		Variable x = queue.pickAndDelete();
		int pm = solver.head.control.varh.pickMode;
		int before = solver.problem.nValueRemovals;
		if (!nogoodReasoning.isNogoodConsistent(x))
			consistent = false;
		else {
			for (Constraint c : x.ctrs) {
				if (!c.ignored && !solver.isEntailed(c)) {
					if (!c.postponable) {
						currFilteringCtr = c;
						int bef = solver.problem.nValueRemovals;
						consistent = c.filterFrom(x);
						if (historyC != null && solver.problem.nValueRemovals > bef)
							historyC.add(c.num, pm == 0 ? 1 : consistent ? solver.problem.nValueRemovals - bef : 100);
						currFilteringCtr = null;
					} else {// if (c.time <= x.time)
						postponedConstraints.add(c); // auxiliaryQueues[c.filteringComplexity - 1].add(c.num, x.num);
						c.postponedEvent = x;
					}
				}
				if (!consistent)
					break;
			}
		}
		if (historyX != null && solver.problem.nValueRemovals > before)
			historyX.add(x.num, pm == 0 ? 1 : consistent ? solver.problem.nValueRemovals - before : 100); // TODO: 100
		return consistent;
	}

	/**
	 * Runs propagation by picking variables from the queue and executing filtering algorithms.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public boolean propagate() {
		if (historyX != null)
			historyX.clear();
		if (historyC != null)
			historyC.clear();
		while (true) {
			while (queue.size() != 0) // propagation with respect to the main queue
				if (pickAndFilter() == false)
					return false;
			for (Constraint c : postponedConstraints) { // propagation with respect to postponed constraints
				assert !c.ignored && !solver.isEntailed(c);
				currFilteringCtr = c;
				int bef = solver.problem.nValueRemovals;
				boolean consistent = c.filterFrom(c.postponedEvent);
				if (historyC != null && solver.problem.nValueRemovals > bef)
					historyC.add(c.num, solver.head.control.varh.pickMode == 0 ? 1 : consistent ? solver.problem.nValueRemovals - bef : 100);
				currFilteringCtr = null;
				if (!consistent)
					return false;
			}
			postponedConstraints.clear();
			// for (SetSparseMap auxiliaryQueue : auxiliaryQueues) // propagation wrt the auxiliary queues
			// while (!auxiliaryQueue.isEmpty()) {
			// int cnum = auxiliaryQueue.shift();
			// int xnum = auxiliaryQueue.values[cnum];
			// Constraint c = solver.problem.constraints[cnum];
			// Variable x = solver.problem.variables[xnum];
			// // TODO : next instruction forces filtering, code may be improved to filter only when necessary
			// c.time = x.time;
			// if (!c.ignored && !solver.isEntailed(c)) { // means that the constraint is ignored or entailed
			// currFilteringCtr = c;
			// boolean consistent = c.filterFrom(x);
			// currFilteringCtr = null;
			// if (!consistent)
			// return false;
			// }
			// // auxiliaryQueue.remove(auxiliaryQueue.dense[0]);
			// }
			if (queue.size() == 0)
				break;
		}
		return true;

	}

	/**
	 * Runs propagation by starting from the specified constraint (calling first its propagator)
	 * 
	 * @param c
	 *            a constraint from which propagation starts
	 * @return false iff an inconsistency is detected
	 */
	public final boolean propagate(ConstraintGlobal c) {
		if (c == null || c.ignored || solver.isEntailed(c))
			return true;
		if (c.runPropagator(null) == false)
			return false;
		return propagate(); // because the queue may be not empty
	}

	/**
	 * This method is called to run constraint propagation, typically at the beginning of search (i.e., in a preprocessing stage), but it can also be called
	 * when at root node of a new run
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runInitially();

	/**
	 * This method is called to possibly run constraint propagation, at the root of the search tree, typically before performing a new run (restart).
	 * 
	 * @return true iff constraint propagation has been rerun
	 */
	public boolean runPossiblyAtRoot() {
		// we rerun propagation if a solution has just been found (since the objective constraint has changed), or if it
		// must be forced anyway
		int numRun = solver.restarter.numRun;
		boolean rerun = runAtNextRoot || (solver.problem.optimizer != null && numRun - 1 == solver.solutions.lastRun)
				|| (options.strongOnce && 0 < numRun && numRun % 60 == 0); // TODO hard coding for 60
		if (rerun) {
			if (runInitially() == false)
				solver.stopping = Stopping.FULL_EXPLORATION;
			runAtNextRoot = false;
		}
		return rerun;
	}

	/**
	 * This method is called after the specified variable has been assigned in order to propagate this event.
	 * 
	 * @param x
	 *            the variable that has just been assigned
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runAfterAssignment(Variable x);

	/**
	 * This method is called when a binary branching scheme is used by the solver. Indeed, after a positive decision (value assigned to a variable), one can
	 * proceed with a negative decision (value removed from the domain of the variable), and to run constraint propagation before selecting another variable.
	 * This method is always called with a variable whose domain is not empty.
	 * 
	 * @param x
	 *            the variable that has just been subject to a refutation (negative decision)
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runAfterRefutation(Variable x);

	/**
	 * To be called when the domain of the specified variable has just been reduced. <br />
	 * Be careful: the domain of the specified variable is not necessarily already reduced, and so may be different from the specified value, which is then
	 * considered as the virtual size of the domain of the specified variable.
	 * 
	 * @param x
	 *            the variable whose domain has just been reduced
	 * @param newDomSize
	 *            the virtual domain size of the specified variable
	 * @return false iff an inconsistency is detected
	 */
	public final boolean handleReduction(Variable x, int newDomSize) {
		if (newDomSize == 0) {
			lastWipeoutVar = x;
			for (ObserverOnConflicts obs : solver.observersOnConflicts)
				obs.whenWipeout(currFilteringCtr, x);
			// queue.clear();
			return false;
		}
		queue.add(x);
		return true;
	}

	/**
	 * To be called when the domain of the specified variable has just been reduced.
	 * 
	 * @param x
	 *            the variable whose domain has just been reduced
	 * @return false iff an inconsistency is detected
	 */
	public final boolean handleReduction(Variable x) {
		return handleReduction(x, x.dom.size());
	}
}
