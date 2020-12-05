/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.Set;
import java.util.stream.IntStream;

import constraints.Constraint;
import constraints.Constraint.CtrGlobal;
import dashboard.Control.SettingPropagation;
import interfaces.Observers.ObserverConflicts;
import sets.SetSparse;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Variable;

/**
 * The root class of all classes that can be used to manage constraint propagation. For simplicity, propagation and consistency concepts are not distinguished,
 * So, some subclasses are given the name of consistencies.
 * 
 * @author lecoutre
 * 
 */
public abstract class Propagation {

	public static Propagation buildFor(Solver solver) {
		if (solver.head.control.solving.enablePrepro || solver.head.control.solving.enableSearch) {
			Set<Class<?>> classes = solver.head.handlerClasses.map.get(Propagation.class);
			return Reflector.buildObject(solver.head.control.propagation.clazz, classes, solver);
		}
		return null;
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/**
	 * The solver to which the propagation object is attached.
	 */
	public final Solver solver;

	/**
	 * The queue (actually, set) used for propagation. During propagation, it contains variables.
	 */
	public final Queue queue;

	/**
	 * Auxiliary queues for handling constraint with expensive propagators. Currently, its usage is experimental.
	 */
	public final SetSparseMap[] auxiliaryQueues;

	/**
	 * This field is used to count time. It is used to avoid performing some useless calls of constraint propagators by comparing time-stamps attached to
	 * variables with time-stamps attached to constraints.
	 * 
	 */
	public long time;

	/**
	 * The constraint that is used currently to filter domains. This is null if no constraint is currently used for filtering. This is relevant for AC.
	 */
	public Constraint currFilteringCtr;

	/**
	 * The variable that has been wiped out the last time constraint propagation led to failure
	 */
	public Variable lastWipeoutVar;

	/**
	 * Metrics for filtering approaches based on singleton tests. Put at the root class for simplicity.
	 */
	public long nSingletonTests, nEffectiveSingletonTests;

	/**
	 * When true, indicates that the object is currently performing a form of search during propagation. This may be the case for some forms of propagation
	 * based on strong consistencies.
	 */
	public boolean performingProperSearch;

	public int nTuplesRemoved;

	protected final SettingPropagation settings;

	/*************************************************************************
	 * Methods
	 *************************************************************************/

	public static class SetSparseMap extends SetSparse {

		public static SetSparseMap[] buildArray(int length, int capacity) {
			return IntStream.range(0, length).mapToObj(i -> new SetSparseMap(capacity)).toArray(SetSparseMap[]::new);
		}

		public final int[] values;

		public SetSparseMap(int capacity, boolean initiallyFull) {
			super(capacity, initiallyFull);
			values = Kit.range(capacity);
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

	public final void reset() {
		queue.clear();
		for (SetSparseMap auxiliaryQueue : auxiliaryQueues)
			auxiliaryQueue.clear();
		nTuplesRemoved = 0;
	}

	/**
	 * Increments the value of the time counter, and returns it.
	 */
	public final long incrementTime() {
		return ++time;
	}

	public Propagation(Solver solver) {
		this.solver = solver;
		this.settings = solver.head.control.propagation;
		this.queue = this instanceof Forward ? new Queue((Forward) this) : null;
		int nAuxQueues = settings.useAuxiliaryQueues ? Constraint.MAX_FILTERING_COMPLEXITY : 0;
		this.auxiliaryQueues = this instanceof Forward ? SetSparseMap.buildArray(nAuxQueues, solver.problem.constraints.length) : null;

	}

	/**
	 * Pick and delete a variable from the queue and call filtering algorithms associated with the constraints involving the variable. Possibly postpone
	 * filtering if auxiliary queues are used.
	 * 
	 * @return false iff an inconsistency is detected
	 */
	protected final boolean pickAndFilter() {
		Variable x = queue.pickAndDelete();
		if (!queue.isNogoodConsistent(x))
			return false;
		for (Constraint c : x.ctrs)
			if (!c.ignored && !solver.isEntailed(c))
				if (c.filteringComplexity == 0) {
					currFilteringCtr = c;
					boolean consistent = c.filterFrom(x);
					currFilteringCtr = null;
					if (!consistent)
						return false;
				} else if (c.time <= x.time)
					auxiliaryQueues[c.filteringComplexity - 1].add(c.num, x.num);
		return true;
	}

	/**
	 * Run propagation by picking variables from the queue and executing filtering algorithms.
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

	public boolean propagate(CtrGlobal c) {
		if (c == null)
			return true;
		if (c.runPropagator(null) == false)
			return false;
		return propagate(); // because the queue may be not empty
	}

	/**
	 * This method is called to run constraint propagation, typically at the beginning of search (i.e., in a preprocessing stage).
	 * 
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runInitially();

	/**
	 * This method is called after the specified variable has been assigned
	 * 
	 * @return false iff an inconsistency is detected
	 */
	/**
	 * This method is called after the specified variable has been assigned in order to propagate it.
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
	 *            the variable that has just been subject to a refutation (negative decision).
	 * @return false iff an inconsistency is detected
	 */
	public abstract boolean runAfterRefutation(Variable x);

	/**
	 * To be called when the domain of the specified variable has just been reduced. <br />
	 * Be careful: the domain of the specified variable is not necessarily already reduced, and so may be different from the specified value newDomSize, which
	 * is the (virtual) size of the domain of the specified variable.
	 */
	public final boolean handleReduction(Variable x, int newDomSize) {
		if (newDomSize == 0) {
			lastWipeoutVar = x;
			for (ObserverConflicts obs : solver.observersConflicts)
				obs.whenWipeout(currFilteringCtr, x);
			// queue.clear();
			return false;
		}
		queue.add(x);
		return true;
	}

	/**
	 * To be called when the domain of the specified variable has just been reduced.
	 */
	public final boolean handleReduction(Variable x) {
		return handleReduction(x, x.dom.size());
	}

	public final boolean handleReductionSafely(Variable x) {
		assert x.dom.size() > 0;
		queue.add(x);
		return true;
	}
}
