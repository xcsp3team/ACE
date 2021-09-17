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

import java.util.stream.IntStream;

import constraints.Constraint;
import constraints.ConstraintGlobal;
import dashboard.Control.SettingPropagation;
import interfaces.Observers.ObserverOnConflicts;
import learning.IpsRecorderForDominance;
import sets.SetSparse;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.Variable;

/**
 * The root class of any object that can be used to manage constraint propagation. For simplicity, propagation and
 * consistency concepts are not distinguished, So, some subclasses are given the name of consistencies.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Propagation {

	/*************************************************************************
	 * Static members
	 *************************************************************************/

	/**
	 * Builds and returns the propagation to be attached to the specified solver. If preprocessing and search stages are
	 * disabled, null is returned.
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

	static class SetSparseMap extends SetSparse {

		public final int[] values;

		public SetSparseMap(int capacity, boolean initiallyFull) {
			super(capacity, initiallyFull);
			this.values = Kit.range(capacity);
		}

		public SetSparseMap(int capacity) {
			this(capacity, false);
		}

		public int valueForPosition(int i) {
			return values[dense[i]];
		}

		@Override
		public final boolean add(int e) {
			throw new RuntimeException("Must not be called without a second argument");
		}

		public boolean add(int e, int value) {
			boolean b = super.add(e);
			values[e] = value; // even if e is already present, the new value is recorded
			return b;
		}
	}

	private class NogoodReasoning {

		private Boolean ipsDominanceReasoning;

		private int[] absentValuesSentinel;

		private long[] sentinelLevel;

		public boolean isNogoodConsistent(Variable x) {
			Domain dom = x.dom;
			if (solver.nogoodRecorder != null)
				if (dom.size() == 1 && solver.nogoodRecorder.checkWatchesOf(x, dom.first(), false) == false)
					return false;
			if (ipsDominanceReasoning == null) { // first call
				ipsDominanceReasoning = solver.ipsRecorder instanceof IpsRecorderForDominance ? Boolean.TRUE : Boolean.FALSE;
				if (ipsDominanceReasoning) {
					this.absentValuesSentinel = new int[solver.problem.variables.length];
					this.sentinelLevel = new long[solver.problem.variables.length];
				}
			}
			if (ipsDominanceReasoning) {
				IpsRecorderForDominance ipsRecorder = (IpsRecorderForDominance) solver.ipsRecorder;
				if (sentinelLevel[x.num] != solver.stats.safeNumber())
					absentValuesSentinel[x.num] = -1;
				int depth = solver.depth();
				int lastRemoved = dom.lastRemoved();
				for (int a = lastRemoved; a != absentValuesSentinel[x.num] && dom.removedLevelOf(a) == depth; a = dom.prevRemoved(a))
					if (!ipsRecorder.checkWatchesOf(x.num, a))
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
	 * Auxiliary queues for handling constraints with different levels of propagator complexities. Currently, its usage
	 * is experimental.
	 */
	public final SetSparseMap[] auxiliaryQueues;

	/**
	 * This field is used as a clock to enumerate time. It is used to avoid performing some useless calls of constraint
	 * propagators by comparing time-stamps attached to variables with time-stamps attached to constraints.
	 * 
	 */
	public long time;

	/**
	 * The constraint that is currently used in propagation. This is null if no constraint is currently used for
	 * filtering. This is relevant for AC.
	 */
	public Constraint currFilteringCtr;

	/**
	 * The variable that has been wiped out the last time constraint propagation led to failure
	 */
	public Variable lastWipeoutVar;

	/**
	 * The object to be used when picking a variable from the queue in order to reason first with recorded nogoods (if
	 * any)
	 */
	private NogoodReasoning nogoodReasoning = new NogoodReasoning();

	/**
	 * When true, indicates that the object is currently performing a form of search during propagation. This may be the
	 * case for some forms of propagation based on strong consistencies.
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
	 * Settings about propagation
	 */
	protected final SettingPropagation settings;

	/*************************************************************************
	 * Methods
	 *************************************************************************/

	public final void reset() {
		queue.clear();
		for (SetSparseMap auxiliaryQueue : auxiliaryQueues)
			auxiliaryQueue.clear();
		nTuplesRemoved = 0;
	}

	/**
	 * Increments the value of the clock (time counter), and returns it.
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
		this.settings = solver.head.control.propagation;
		int nAuxQueues = settings.useAuxiliaryQueues ? Constraint.MAX_FILTERING_COMPLEXITY : 0;
		this.auxiliaryQueues = this instanceof Forward
				? IntStream.range(0, nAuxQueues).mapToObj(i -> new SetSparseMap(solver.problem.constraints.length)).toArray(SetSparseMap[]::new)
				: null;
	}

	/**
	 * Pick and delete a variable from the queue and call filtering algorithms associated with the constraints involving
	 * the variable. Possibly postpone filtering if auxiliary queues are used.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean pickAndFilter() {
		Variable x = queue.pickAndDelete();
		if (!nogoodReasoning.isNogoodConsistent(x))
			return false;
		for (Constraint c : x.ctrs)
			if (!c.ignored && !solver.isEntailed(c)) {
				if (c.filteringComplexity == 0) {
					currFilteringCtr = c;
					boolean consistent = c.filterFrom(x);
					currFilteringCtr = null;
					if (!consistent)
						return false;
				} else if (c.time <= x.time)
					auxiliaryQueues[c.filteringComplexity - 1].add(c.num, x.num);
			}
		return true;
	}

	/**
	 * Runs propagation by picking variables from the queue and executing filtering algorithms.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public boolean propagate() {
		while (true) {
			while (queue.size() != 0) // propagation wrt the main queue
				if (pickAndFilter() == false)
					return false;
			for (SetSparseMap auxiliaryQueue : auxiliaryQueues) // propagation wrt the auxiliary queues
				while (!auxiliaryQueue.isEmpty()) {
					int cnum = auxiliaryQueue.shift();
					int xnum = auxiliaryQueue.values[cnum];
					Constraint c = solver.problem.constraints[cnum];
					Variable x = solver.problem.variables[xnum];
					// TODO : next instruction forces filtering, code may be improved to filter only when necessary
					c.time = x.time;
					if (!c.ignored && !solver.isEntailed(c)) { // means that the constraint is ignored or entailed
						currFilteringCtr = c;
						boolean consistent = c.filterFrom(x);
						currFilteringCtr = null;
						if (!consistent)
							return false;
					}
					// auxiliaryQueue.remove(auxiliaryQueue.dense[0]);
				}
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
	 * This method is called to run constraint propagation, typically at the beginning of search (i.e., in a
	 * preprocessing stage).
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runInitially();

	/**
	 * This method is called after the specified variable has been assigned in order to propagate this event.
	 * 
	 * @param x
	 *            the variable that has just been assigned
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runAfterAssignment(Variable x);

	/**
	 * This method is called when a binary branching scheme is used by the solver. Indeed, after a positive decision
	 * (value assigned to a variable), one can proceed with a negative decision (value removed from the domain of the
	 * variable), and to run constraint propagation before selecting another variable. This method is always called with
	 * a variable whose domain is not empty.
	 * 
	 * @param x
	 *            the variable that has just been subject to a refutation (negative decision)
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runAfterRefutation(Variable x);

	/**
	 * To be called when the domain of the specified variable has just been reduced. <br />
	 * Be careful: the domain of the specified variable is not necessarily already reduced, and so may be different from
	 * the specified value, which is then considered as the virtual size of the domain of the specified variable.
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
