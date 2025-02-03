/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import static org.xcsp.common.Constants.ALL;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.common.enumerations.EnumerationCartesian;
import org.xcsp.modeler.definitions.ICtr;

import constraints.ConstraintIntension.IntensionStructure;
import constraints.extension.structures.Bits;
import constraints.extension.structures.ExtensionStructure;
import constraints.global.Sum.SumSimple.SumSimpleEQ;
import constraints.global.Sum.SumWeighted.SumWeightedEQ;
import dashboard.Control.OptionsConstraints;
import dashboard.Control.OptionsPropagation;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import interfaces.Observers.ObserverOnConstruction;
import interfaces.SpecificPropagator;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import interfaces.Tags.TagPostponableFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import propagation.Forward;
import propagation.Reviser;
import propagation.Supporter;
import sets.SetDense;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.DomainInfinite;
import variables.TupleIterator;
import variables.Variable;

/**
 * A constraint is attached to a problem, involves a subset of variables of the problem, and allows us to reason so as to filter the search space (i.e., the
 * domains of the variables). A variable is uniquely identified by a number (field <code>num</code>).
 * 
 * @author Christophe Lecoutre
 */
public abstract class Constraint implements ObserverOnConstruction, Comparable<Constraint>, ICtr {

	/*************************************************************************
	 ***** Implementing Interfaces
	 *************************************************************************/

	@Override
	public int compareTo(Constraint c) {
		boolean b1 = id == null, b2 = c.id == null; // b1 and b2 true iff canonical ids
		return b1 && !b2 ? -1 : !b1 && b2 ? 1 : !b1 && !b2 ? id.compareTo(c.id) : Integer.compare(num, c.num);
	}

	@Override
	public void afterProblemConstruction(int n) {
		int r = scp.length;
		if (options.positionsLb <= r && (n < options.positionsUb || r > n / 3)) { // TODO hard coding (3)
			this.positions = Kit.repeat(-1, n); // if a variable is not involved, then its position is set to -1
			for (int i = 0; i < r; i++)
				this.positions[scp[i].num] = i;
			this.futvars = new SetSparse(r, true);
		} else {
			this.positions = null;
			this.futvars = new SetDense(r, true);
		}
	}

	/*************************************************************************
	 ***** Two very special constraints called CtrFalse and CtrTrue
	 *************************************************************************/

	/**
	 * A class for trivial constraints never satisfied or always satisfied (to be used in very special situations)
	 */
	public static abstract class CtrTrivial extends Constraint implements SpecificPropagator, TagAC, TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return value;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			return value;
		}

		/**
		 * The trivial value (false or true) of the constraint
		 */
		private boolean value;

		/**
		 * A message indicating the reason why such a constraint is built
		 */
		public String message;

		public CtrTrivial(Problem pb, Variable[] scp, boolean value, String message) {
			super(pb, scp);
			this.value = value;
			this.message = message;
		}

		/**
		 * A class for never satisfied constraints (to be used in very special situations)
		 */
		public static final class CtrFalse extends CtrTrivial {

			public CtrFalse(Problem pb, Variable[] scp, String message) {
				super(pb, scp, false, message);
			}
		}

		/**
		 * A class for always satisfied constraints (to be used in very special situations)
		 */
		public static final class CtrTrue extends CtrTrivial {

			public CtrTrue(Problem pb, Variable[] scp, String message) {
				super(pb, scp, true, message);
			}
		}
	}

	/*************************************************************************
	 ***** Static members
	 *************************************************************************/

	/**
	 * A special constraint that can be used (for instance) by methods that requires returning three-state values: null, a classical constraint, and this
	 * special constraint/marker.
	 */
	public static final Constraint TAG = new Constraint() {
		@Override
		public boolean isSatisfiedBy(int[] t) {
			throw new AssertionError("should not be called");
		}
	};

	/**
	 * Returns true if the num(ber)s of the constraints in the specified array are normalized, meaning that the num(ber) of the constraint at index i of the
	 * array is i.
	 * 
	 * @param ctrs
	 *            an array of constraints
	 * @return true if the num(ber)s of the constraints in the specified array are normalized
	 */
	public static final boolean areNumsNormalized(Constraint[] ctrs) {
		return IntStream.range(0, ctrs.length).noneMatch(i -> i != ctrs[i].num);
	}

	/**
	 * Computes the greatest number k such that, whatever is the selection of k integers in the specified array, the number of tuples that can be built by
	 * considering sets of these selected sizes does not exceed the specified limit.
	 * 
	 * @param sizes
	 *            an array of integers representing the sizes of sets (domains)
	 * @param limit
	 *            a limit in term of number of tuples
	 */
	private static final int howManyVariablesWithin(int[] sizes, double limit) {
		control(limit > 1);
		Arrays.sort(sizes);
		double prod = 1;
		for (int i = sizes.length - 1; i >= 0 && prod <= limit; i--) {
			prod = prod * sizes[i];
			if (prod > limit)
				return sizes.length - i - 1;
		}
		return ALL;
	}

	/**
	 * Computes the greatest number k of variables such that, whatever is the selection of k variables in the specified array, the size of the Cartesian product
	 * of the domains of these variables does not exceed 2 to the power of the specified exponent.
	 * 
	 * @param vars
	 *            an array of variables
	 * @param exponent
	 *            a limit (equal to 2 to the power given by this exponent) in term of number of tuples
	 * @return the greatest number of variables ensuring that any selection of this size does not exceed the specified limit
	 */
	public static final int howManyVariablesWithin(Variable[] vars, int exponent) {
		if (exponent == 0)
			return 0;
		return howManyVariablesWithin(Stream.of(vars).filter(x -> x != null).mapToInt(x -> x.dom.size()).toArray(), Math.pow(2, exponent));
	}

	public static final int computeGenericFilteringThreshold(Variable[] vars) {
		OptionsPropagation options = vars[0].problem.head.control.propagation;
		if (options.arityLimit == -1 || vars.length <= options.arityLimit || options.spaceLimit == -1)
			return Integer.MAX_VALUE; // meaning no threshold
		return Math.max(options.arityLimit, howManyVariablesWithin(vars, options.spaceLimit));
	}

	/**
	 * @param ctrs
	 *            an array of constraints
	 * @param instantiation
	 *            an instantiation (containing indexes of values) to be checked (possibly, null)
	 * @return the first unsatisfied constraint in the specified array with respect to the specified instantiation (or with respect to the current instantiation
	 *         of the involved variables if the specified instantiation is null), or null if there is none
	 */
	public static final Constraint firstUnsatisfiedConstraint(Constraint[] ctrs, int[] instantiation) {
		for (Constraint c : ctrs) {
			if (c.ignored)
				continue;
			int[] t = c.tupleIterator.buffer;
			for (int i = 0; i < t.length; i++)
				t[i] = instantiation != null ? instantiation[c.scp[i].num] : c.scp[i].dom.single();
			if (c.checkIndexes(t) == false)
				return c;
		}
		return null;
	}

	/**
	 * @param ctrs
	 *            an array of constraints
	 * @return the first unsatisfied constraint in the specified array with respect to the current instantiation of the variables involved in the constraints
	 */
	public static final Constraint firstUnsatisfiedConstraint(Constraint[] ctrs) {
		return firstUnsatisfiedConstraint(ctrs, null);
	}

	/**
	 * @param ctrs
	 *            an array of constraints
	 * @return the sum of costs of all constraints in the specified array that are covered by the current instantiation
	 */
	public static final long costOfCoveredConstraintsIn(Constraint[] ctrs) {
		// note that using streams is costly
		long cost = 0;
		for (Constraint c : ctrs)
			if (!c.ignored && c.futvars.size() == 0)
				cost = Kit.addSafe(cost, c.costOfCurrentInstantiation());
		return cost;
	}

	/**
	 * Builds and returns a table with all tuples (instantiations) satisfying the specified constraints. Note that it may lead to a combinatorial explosion.
	 * 
	 * @param ctrs
	 *            an array of constraints
	 * @return a table with all tuples (instantiations) satisfying the specified constraints
	 */
	public static final int[][] buildTable(Constraint... ctrs) {
		Variable[] scp = Variable.scopeOf(ctrs);
		int[][] positions = Stream.of(ctrs).map(c -> Stream.of(c.scp).mapToInt(x -> Utilities.indexOf(x, scp)).toArray()).toArray(int[][]::new);
		List<int[]> list = new ArrayList<>();
		int[] support = new int[scp.length];
		EnumerationCartesian ec = new EnumerationCartesian(Stream.of(scp).mapToInt(x -> x.dom.initSize()).toArray());
		start: while (ec.hasNext()) {
			int[] indexes = ec.next();
			for (int i = 0; i < ctrs.length; i++) {
				int[] t = ctrs[i].tupleIterator.buffer;
				for (int j = 0; j < t.length; j++)
					t[j] = indexes[positions[i][j]];
				if (!ctrs[i].checkIndexes(t))
					continue start;
			}
			for (int i = 0; i < indexes.length; i++)
				support[i] = scp[i].dom.toVal(indexes[i]);
			list.add(support.clone()); // cloning is necessary
		}
		return list.stream().toArray(int[][]::new);
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/**
	 * The problem to which the constraint belongs.
	 */
	public final Problem problem;

	/**
	 * The number of the constraint; it is -1 when not fully initialized or not a direct constraint of the problem.
	 */
	public int num = -1;

	/**
	 * The id (identifier or name) of the constraint.
	 */
	private String id;

	/**
	 * The scope of the constraint, i.e. the set of variables involved in the constraint.
	 */
	public final Variable[] scp;

	/**
	 * doms[i] is the domain of scp[i] (redundant field)
	 */
	public final Domain[] doms;

	/**
	 * The position of all variables of the problem in the constraint. It is -1 when not involved. For constraint of small arity, this array is not necessarily
	 * built. So, you need to call <code> positionOf </code> instead of accessing directly this field.
	 */
	private int[] positions;

	/**
	 * A dense set for storing (the positions in scp of) the variables that are not explicitly assigned by the solver
	 */
	public SetDense futvars;

	/**
	 * The object that can be used to iterate over the (valid) tuples of the Cartesian product of the domains of the constraint scope.
	 */
	public final TupleIterator tupleIterator;

	/**
	 * An object that can be useful to look efficiently after supports (using a cache technique called residues); useful only with some kind of constraints
	 */
	protected final Supporter supporter;

	/**
	 * The object that manages information about the number of conflicts of pairs (x,a) for the constraint; useful only with some kind of constraints
	 */
	public ConflictsStructure conflictsStructure;

	/**
	 * Indicates if for each domain of a variable involved in the constraint, the index of any value is equal to this value.
	 */
	public final boolean indexesMatchValues;

	/**
	 * Indicates if the constraint must be ignored (may be useful in some specific situations).
	 */
	public boolean ignored;

	public final boolean postponable;

	public Variable postponedEvent;

	/**
	 * The key of the constraint. This field is only used for symmetry detection, when activated.
	 */
	private String key;

	/**
	 * The (dissatisfaction) cost of the constraint when it is not satisfied
	 */
	public int cost = 1;

	/**
	 * The last time the constraint was solicited for filtering
	 */
	public long time;

	/**
	 * Indicates if filtering (e.g. AC) must be controlled. If the number of uninstantiated variables is greater than this value, filtering is not achieved;
	 * useful only with some kind of constraints
	 */
	public final int genericFilteringThreshold;

	/**
	 * The number of times the constraint has been effective when solicited for filtering
	 */
	public int nEffectiveFilterings;

	/**
	 * The array of variables with infinite domains. Currently, not used.
	 */
	public Variable[] infiniteDomainVars;

	/**
	 * The options concerning constraints
	 */
	public OptionsConstraints options;

	/**
	 * This field is used to store a tuple of (int) values. Is is inserted as a field in order to avoid overhead of memory allocations.
	 */
	protected final int[] vals;

	/**********************************************************************************************
	 * General methods
	 *********************************************************************************************/

	/**
	 * Returns the identifier of the constraint, either an explicitly defined (in field id) or a default one
	 * 
	 * @return the identifier of the constraint
	 */
	public final String getId() {
		return id != null ? id : "c" + num;
	}

	/**
	 * Returns the key associated with the constraint; useful for symmetry-breaking
	 * 
	 * @return the key of the constraint
	 */
	public final String getKey() {
		if (key == null)
			defineKey(); // without any parameter
		return key;
	}

	/**
	 * Defines the key of the constraint from the signature, the type of the domains, and the specified data. Keys are currently used for deciding if two
	 * constraints can share some structures (this is the case when they have the same keys), and also for symmetry-breaking.
	 * 
	 * @param data
	 *            a sequence of objects that must be considered to form the key of the constraint
	 * @return the key
	 */
	protected final String defineKey(Object... data) {
		control(this.key == null, "should not be called twice");
		StringBuilder sb = signature();
		for (Object obj : data)
			sb.append('|').append(obj instanceof Collection ? Kit.join((Collection<?>) obj) : obj.getClass().isArray() ? Kit.join(obj) : obj.toString());
		this.key = sb.toString();
		return this.key;
	}

	/**
	 * @param x
	 *            a variable
	 * @return the position of the variable in the scope of the constraint, or -1
	 */
	public final int positionOf(Variable x) {
		if (positions != null)
			return positions[x.num];
		for (int i = scp.length - 1; i >= 0; i--)
			if (scp[i] == x)
				return i;
		return -1;
	}

	/**
	 * @param x
	 *            a variable
	 * @return true if the the specified variable is involved in this constraint
	 */
	public final boolean involves(Variable x) {
		return positionOf(x) != -1;
	}

	/**
	 * @param presentVars
	 *            an array of Boolean, one for each variable of the problem
	 * @return true if any variable involved in the constraint is such that the corresponding Boolean in the specified array is true
	 */
	public final boolean isScopeCoveredBy(boolean[] presentVars) {
		for (Variable x : scp)
			if (!presentVars[x.num])
				return false;
		return true;
	}

	/**
	 * @return the number of free variables (i.e., with non singleton domains) involved in the constraint
	 */
	public final int nFreeVariables() {
		int cnt = 0;
		for (int i = futvars.limit; i >= 0; i--)
			if (scp[futvars.dense[i]].dom.size() > 1)
				cnt++;
		return cnt;
	}

	/**
	 * @return the weighted degree of the constraint
	 */
	public final double wdeg() {
		return ((WdegVariant) problem.solver.heuristic).cscores[num];
	}

	/**
	 * Returns true if the constraint is irreflexive. Currently, this can be only called on binary constraints, but certainly could be generalized.
	 * 
	 * @return true if the constraint is irreflexive
	 */
	public final boolean isIrreflexive() {
		control(scp.length == 2);
		int[] tuple = tupleIterator.buffer;
		int x = scp[0].dom.size() > scp[1].dom.size() ? 1 : 0, y = x == 0 ? 1 : 0;
		Domain dx = scp[x].dom, dy = scp[y].dom;
		for (int a = dx.first(); a != -1; a = dx.next(a)) {
			int b = dy.toIdx(dx.toVal(a));
			if (b < 0)
				continue;
			tuple[x] = a;
			tuple[y] = b;
			if (checkIndexes(tuple))
				return false;
		}
		return true;
	}

	/**
	 * Returns true if a is substitutable by b for x on this constraint
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            a first value index
	 * @param b
	 *            a second value index
	 * @return true if a is substitutable by b for x on this constraint
	 */
	public final boolean isSubstitutableBy(int x, int a, int b) {
		tupleIterator.firstValidTupleWith(x, a);
		return !tupleIterator.findValidTupleChecking(t -> {
			t[x] = a;
			boolean b1 = checkIndexes(t);
			t[x] = b;
			boolean b2 = checkIndexes(t);
			return b1 && !b2;
		});
	}

	/**
	 * @return true if (G)AC is guaranteed by this constraint
	 */
	public boolean isGuaranteedAC() {
		if (this.infiniteDomainVars.length > 0)
			return false;
		if (this instanceof TagAC)
			return true;
		if (this instanceof TagNotAC)
			return false;
		if (this instanceof SpecificPropagator)
			// exception launched to force the user to tag constraints or override the function
			throw new UnsupportedOperationException(getClass().getName());
		return genericFilteringThreshold == Integer.MAX_VALUE;
	}

	/**
	 * @return true if the constraint is symmetric, false if it is not, and null if undetermined
	 */
	public Boolean isSymmetric() {
		if (this instanceof TagSymmetric)
			return Boolean.TRUE;
		if (this instanceof TagNotSymmetric)
			return Boolean.FALSE;
		return null;
	}

	/**
	 * @return an array with colors (integers) showing which variables are locally symmetric
	 */
	public int[] symmetryMatching() { // default method that can be redefined
		Boolean b = isSymmetric();
		// if (b == null)
		// return Kit.series(1, scp.length);
		control(b != null, "constraint " + this);
		return b ? Kit.repeat(1, scp.length) : Kit.series(1, scp.length);
	}

	/**
	 * @return sets this constraint as being entailed (if not yet), and returns true  
	 */
	public final boolean entail() {
		problem.solver.entail(this);
		return true;
	}

	/**
	 * Returns the intension structure (i.e., object to evaluate a Boolean expression tree) if this object is an intension constraint, null otherwise
	 * 
	 * @return the extension structure if this object is an intension constraint, or null
	 */
	public IntensionStructure intStructure() {
		return null;
	}

	/**
	 * Returns the extension structure (i.e., object like a table) if this object is an extension constraint, null otherwise
	 * 
	 * @return the extension structure if this object is an extension constraint, or null
	 */
	public ExtensionStructure extStructure() {
		return null;
	}

	/**
	 * Clone some shared structures.
	 * 
	 * @param onlyConflicts
	 *            when true, shared structures other than conflicts structures must also be cloned
	 */
	public void cloneStructures(boolean onlyConflicts) {
		if (conflictsStructure != null && conflictsStructure.registeredCtrs().size() > 1) {
			conflictsStructure.unregister(this);
			conflictsStructure = new ConflictsStructure(this, conflictsStructure);
		}
	}

	/**********************************************************************************************
	 * Constructors
	 *********************************************************************************************/

	/**
	 * Private constructor just used to build the TAG constraint.
	 */
	private Constraint() {
		this.problem = null;
		this.scp = new Variable[0];
		this.doms = null;
		this.tupleIterator = null;
		this.vals = null;
		this.genericFilteringThreshold = Integer.MAX_VALUE;
		this.indexesMatchValues = false;
		this.postponable = false;
		this.infiniteDomainVars = new Variable[0];
		this.supporter = null;
	}

	/**
	 * Build a constraint for the specified problem, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public Constraint(Problem pb, Variable[] scp) {
		this.problem = pb;
		this.scp = scp = Stream.of(scp).distinct().toArray(Variable[]::new); // IMPORTANT: this.scp and scp both updated
		control(scp.length >= 1 && Stream.of(scp).allMatch(x -> x != null), () -> " constraint with a scope badly formed ");

		this.doms = Stream.of(scp).map(x -> x.dom).toArray(Domain[]::new);

		this.tupleIterator = new TupleIterator(this.doms);
		this.supporter = Supporter.buildFor(this);

		this.indexesMatchValues = Stream.of(scp).allMatch(x -> x.dom.indexesMatchValues());
		this.genericFilteringThreshold = this instanceof SpecificPropagator || this instanceof ConstraintExtension ? Integer.MAX_VALUE
				: computeGenericFilteringThreshold(scp);
		this.postponable = scp.length >= pb.head.control.propagation.postponableLimit && pb.head.control.propagation.postponableLimit > 0
				&& this instanceof TagPostponableFiltering;

		pb.head.observersConstruction.add(this);

		this.infiniteDomainVars = Stream.of(scp).filter(x -> x.dom instanceof DomainInfinite).toArray(Variable[]::new);
		this.vals = new int[scp.length];
		this.options = pb.head.control.constraints;
	}

	public final void reset() {
		control(futvars.isFull());
		nEffectiveFilterings = 0;
		time = 0;
	}

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	/**
	 * Records the fact that the specified variable is now a past variable (i.e., explicitly assigned by the solver)
	 * 
	 * @param x
	 *            the variable that has been explicitly assigned
	 */
	public final void doPastVariable(Variable x) {
		// if (!ignored)
		if (positions != null)
			((SetSparse) futvars).remove(positions[x.num]);
		else
			for (int i = futvars.limit; i >= 0; i--) {
				if (scp[futvars.dense[i]] == x) {
					futvars.removeAtPosition(i);
					break;
				}
			}
	}

	/**
	 * Records the fact that the specified variable is not more a past variable (i.e., no more explicitly assigned by the solver)
	 * 
	 * @param x
	 *            the variable that is no more explicitly assigned
	 */
	public final void undoPastVariable(Variable x) {
		// if (!ignored) {
		assert x.assigned() && scp[futvars.dense[futvars.size()]] == x;
		futvars.limit++;
		// }
	}

	/**
	 * Determines if the specified tuple satisfies the constraint, i.e., if the specified tuple belongs to the relation defining the constraint. Be careful:
	 * although indexes of values are managed in the core of the solver, at this stage, the given tuple contains values (and not indexes of values).
	 * 
	 * @param t
	 *            a tuple of values
	 * @return true if the specified tuple of values satisfies the constraint
	 */
	public abstract boolean isSatisfiedBy(int[] t);

	/**
	 * Determines if the specified tuple corresponds to a support of the constraint, i.e., if the tuple of values corresponding to the indexes in the specified
	 * tuple satisfies the constraint. Be careful: the given tuple must contains indexes of values.
	 * 
	 * @param t
	 *            a tuple of indexes (of values)
	 * @return true if the tuple of values corresponding to the specified tuple of indexes satisfies the constraint
	 */
	public boolean checkIndexes(int[] t) {
		if (indexesMatchValues)
			return isSatisfiedBy(t);
		for (int i = vals.length - 1; i >= 0; i--) // we use the local array vals
			vals[i] = doms[i].toVal(t[i]);
		return isSatisfiedBy(vals);
	}

	/**
	 * Returns a tuple with the indexes of the values of the current instantiation of the variables in the constraint scope
	 * 
	 * @return a tuple with the indexes of the values of the current instantiation of the variables in the constraint scope
	 */
	private final int[] instantiationIndexes() {
		int[] t = tupleIterator.buffer;
		for (int i = t.length - 1; i >= 0; i--)
			t[i] = doms[i].single();
		return t;
	}

	/**
	 * Returns true if the current instantiation of the variables of the constraint scope satisfies the constraint. IMPORTANT: all variables of the constraint
	 * scope must be fixed (i.e., with singleton domains).
	 * 
	 * @return true if the current instantiation of the variables of the constraint scope satisfies the constraint
	 */
	public final boolean isSatisfiedByCurrentInstantiation() {
		return checkIndexes(instantiationIndexes());
	}

	/**
	 * Returns 0 if the constraint is satisfied by the current instantiation, or the cost that is associated with the constraint, otherwise. IMPORTANT: all
	 * variables of the constraint scope must be fixed (i.e., with singleton domains).
	 * 
	 * @return 0 if the constraint is satisfied by the current instantiation, or the cost that is associated with the constraint
	 */
	public final long costOfCurrentInstantiation() {
		return checkIndexes(instantiationIndexes()) ? 0 : cost;
	}

	public int giveMostPromisingValueIndexFor(Variable x, boolean anti) {
		return -1;
	}

	/**
	 * Determines if the specified tuple of indexes (usually a support) is still valid. We have just to test that all indexes are still in the domains of the
	 * variables involved in the constraint. Do not call the <code> isSatisfiedBy </code> method instead since it does not take removed values into account.
	 * 
	 * @param t
	 *            a tuple of indexes (of values)
	 * @return <code> true </code> if the specified tuple of indexes is valid
	 */
	public final boolean isValid(int[] t) {
		for (int i = t.length - 1; i >= 0; i--)
			if (!doms[i].contains(t[i]))
				return false;
		return true;
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint) for the constraint when considering the current state of the domains and the tuple
	 * currently managed by the tuple iterator (this current tuple included in the search). A lexicographic order is used.
	 * 
	 * @return true if a support can be found from the current tuple managed by the object 'tupleIterator'
	 */
	private final boolean seekSupport() {
		return tupleIterator.findValidTupleSatisfying(this);
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order, and returns true is such a support can be found
	 * 
	 * @return true if a support can be found
	 */
	public final boolean seekFirstSupport() {
		tupleIterator.firstValidTuple();
		return seekSupport();
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the requirement that the support involves
	 * the specified pair (x,a), and returns true is such a support can be found
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @return true if a support can be found involving the specified pair (x,a)
	 */
	public final boolean seekFirstSupportWith(int x, int a) {
		tupleIterator.firstValidTupleWith(x, a);
		return seekSupport();
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the requirement that the support involves
	 * the specified pair (x,a), and returns true is such a support can be found. The support (containing indexes of values instead of values) is recorded in
	 * the specified buffer.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @param buffer
	 *            an array where to store the support (containing indexes of values instead of values)
	 * @return true if a support can be found involving the specified pair (x,a)
	 */
	public boolean seekFirstSupportWith(int x, int a, int[] buffer) {
		tupleIterator.firstValidTupleWith(x, a, buffer);
		return seekSupport();
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the requirement that the support involves
	 * the specified pairs (x,a) and (y,b), and returns true is such a support can be found. T
	 * 
	 * @param x
	 *            a first variable
	 * @param a
	 *            an index (of value) for the first variable
	 * @param y
	 *            a second variable
	 * @param b
	 *            an index (of value) for the second variable
	 * @return true if a support can be found involving the specified pairs (x,a) and (y,b)
	 */
	public final boolean seekFirstSupportWith(int x, int a, int y, int b) {
		tupleIterator.firstValidTupleWith(x, a, y, b);
		return seekSupport();
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the requirement that the support must come
	 * after the current tuple (excluded) managed by the tuple iterator, and returns true is such a support can be found. Note that the current tuple (of the
	 * tuple iterator) is not necessarily valid (as it may have been deleted). Besides, if some values have been fixed in the tuple iterator, they remain fixed.
	 * 
	 * @return true if another support can be found from the current tuple (excluded) managed by the tuple iterator
	 */
	public final boolean seekNextSupport() {
		return tupleIterator.nextValidTupleCautiously() != -1 && seekSupport();
	}

	/**
	 * Seeks a conflict (i.e., a valid tuple not satisfying the constraint) for the constraint when considering the current state of the domains and the tuple
	 * currently managed by the tuple iterator (this current tuple included in the search). A lexicographic order is used.
	 * 
	 * @return true if a conflict can be found from the current tuple managed by the object 'tupleIterator'
	 */
	private final boolean seekConflict() {
		return tupleIterator.findValidTupleNotSatisfying(this);
	}

	/**
	 * Seeks a conflict (i.e., a valid tuple not satisfying the constraint), while considering a lexicographic order, and returns true is such a conflict can be
	 * found
	 * 
	 * @return true if a conflict can be found
	 */
	public final boolean seekFirstConflict() {
		tupleIterator.firstValidTuple();
		return seekConflict();
	}

	/**
	 * Seeks a conflict (i.e., a valid tuple not satisfying the constraint), while considering a lexicographic order and the requirement that the conflict
	 * involves the specified pair (x,a), and returns true is such a conflict can be found
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @return true if a conflict can be found involving the specified pair (x,a)
	 */
	public final boolean seekFirstConflictWith(int x, int a) {
		tupleIterator.firstValidTupleWith(x, a);
		return seekConflict();
	}

	/**
	 * Returns the number of conflicts (i.e., valid tuples not satisfying the constraint) involving the specified pair (x,a)
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @return the number of conflicts involving the specified pair (x,a)
	 */
	public final long nConflictsFor(int x, int a) {
		tupleIterator.firstValidTupleWith(x, a);
		return tupleIterator.countValidTuplesChecking(t -> !checkIndexes(t));
	}

	public final boolean findArcSupportFor(int x, int a) {
		if (supporter != null)
			return supporter.findArcSupportFor(x, a);
		if (extStructure() instanceof Bits) {
			long[] t1 = ((Bits) extStructure()).sups(x)[a];
			long[] t2 = scp[x == 0 ? 1 : 0].dom.binary();
			for (int i = 0; i < t1.length; i++) {
				if ((t1[i] & t2[i]) != 0)
					return true;
			}
			return false;
		}
		// AC3 below
		return seekFirstSupportWith(x, a);
	}

	/**********************************************************************************************
	 * Methods related to filtering
	 *********************************************************************************************/

	// EXPERIMENTAL not finalized
	private boolean handleHugeDomains() {
		assert infiniteDomainVars.length > 0;
		// TODO huge domains are not finalized
		if (futvars.size() == 0)
			return isSatisfiedByCurrentInstantiation();
		if (futvars.size() == 1) {
			if (this instanceof SumSimpleEQ) {
				((SumSimpleEQ) this).deduce();
				return true;
			}
			if (this instanceof SumWeightedEQ) {
				((SumWeightedEQ) this).deduce();
				return true;
			}
		}
		// for (Variable y : hugeDomainVars)
		// if (!y.isAssigned()) return true; // we have to wait
		if (futvars.size() > 0)
			return true;
		return false;
	}

	/**
	 * Performs a generic form of filtering
	 * 
	 * @param x
	 *            a variable whose domain has been recently reduced
	 * @return false if an inconsistency is detected
	 */
	private boolean genericFiltering(Variable x) {
		if (futvars.size() > genericFilteringThreshold)
			return true;
		Reviser reviser = ((Forward) problem.solver.propagation).reviser;
		if (x.assigned()) {
			for (int i = futvars.limit; i >= 0; i--)
				if (reviser.revise(this, scp[futvars.dense[i]]) == false)
					return false;
		} else {
			boolean revisingEventVarToo = (scp.length == 1); // TODO can we just initialize it to false ?
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y == x)
					continue;
				if (time < y.time)
					revisingEventVarToo = true;
				if (reviser.revise(this, y) == false)
					return false;
			}
			if (revisingEventVarToo && reviser.revise(this, x) == false)
				return false;
		}
		return true;
	}

	/**
	 * This is the method that is called for filtering domains. We know that the domain of the specified variable has been recently reduced, but this is not
	 * necessarily the only one.
	 * 
	 * @param x
	 *            a variable whose domain has been recently reduced
	 * @return false if an inconsistency is detected
	 */
	public final boolean filterFrom(Variable x) {
		// System.out.println("filtering " + " " + x + " " + getClass().getSimpleName() + " " + this + " " + Variable.nValidValuesFor(problem.variables));
		if (infiniteDomainVars.length > 0 && handleHugeDomains()) // Experimental (to be finished)
			return true;
		// For CSP, sometimes we can directly return true (because we know then that there is no filtering possibility)
		if (problem.framework == TypeFramework.CSP) {
			// TODO if the condition is replaced by != TypeFramework.MACSP, there is a pb with:
			// java -ea ac PlaneparkingTask.xml -ea -cm=false -ev -trace
			// possibly too with GraphColoring-sum-GraphColoring_1-fullins-3.xml.lzma
			if (futvars.size() == 0) {
				assert !isGuaranteedAC() || isSatisfiedByCurrentInstantiation() : "Unsatisfied constraint " + this + "while AC should be guaranteed";
				return isGuaranteedAC() || isSatisfiedByCurrentInstantiation();
			}
			if (futvars.size() == 1 && !x.assigned() && scp.length > 1)
				return true;
		}
		if (time > x.time && this instanceof TagCallCompleteFiltering && !(this instanceof TagNotCallCompleteFiltering) && !postponable)
			return true;
		int nBefore = problem.nValueRemovals;
		if (problem.solver.profiler != null)
			problem.solver.profiler.beforeFiltering(this);
		boolean consistent = this instanceof SpecificPropagator ? ((SpecificPropagator) this).runPropagator(x) : genericFiltering(x);
		if (problem.solver.profiler != null)
			problem.solver.profiler.afterFiltering(this);
		if (!consistent || problem.nValueRemovals != nBefore) {
			if (problem.solver.proofer != null)
				problem.solver.proofer.updateProof(this);// TODO // ((SystematicSolver)solver).updateProofAll();
			nEffectiveFilterings++;
			problem.features.nEffectiveFilterings++;
		}
		time = problem.solver.propagation.incrementTime();
		return consistent;
	}

	/**
	 * Returns true if the constraint is AC. IMPORTANT: the control is incomplete. The constraint can be currently ignored, and the test is not performed if the
	 * number of valid tuples is too large.
	 * 
	 * @return true if the constraint is AC
	 */
	public boolean controlAC() {
		if (ignored)
			return true;
		if (Domain.nValidTuplesBounded(doms) > 1000)
			return true;
		for (int x = 0; x < scp.length; x++)
			for (int a = doms[x].first(); a != -1; a = doms[x].next(a))
				if (seekFirstSupportWith(x, a) == false) {
					System.out.println(" " + scp[x] + "=" + doms[x].toVal(a) + " not supported by " + this);
					for (Domain dom : doms)
						dom.display(1);
					display(true);
					return false;
				}
		return true;
	}

	/**********************************************************************************************
	 * Control and display
	 *********************************************************************************************/

	/**
	 * Returns the signature of the constraint, obtained by concatenating the name of its class with the signature of the involved variables
	 * 
	 * @return the signature of the constraint
	 */
	public StringBuilder signature() {
		return Variable.signatureFor(scp).insert(0, " ").insert(0, this.getClass().getSimpleName());
	}

	@Override
	public String toString() {
		return getId() + "(" + Stream.of(scp).map(x -> x.id()).collect(Collectors.joining(",")) + ")";
	}

	/**
	 * Displays information about the constraint
	 * 
	 * @param exhaustively
	 *            true if detailed information must be displayed
	 */
	public void display(boolean exhaustively) {
		Kit.log.finer("Constraint " + toString());
		Kit.log.finer("\tClass = " + getClass().getName()
				+ (this instanceof ConstraintExtension ? ":" + ((ConstraintExtension) this).extStructure().getClass().getSimpleName() : ""));
		if (this instanceof ConstraintIntension)
			Kit.log.finer("\tPredicate: " + ((ConstraintIntension) this).tree.toFunctionalExpression(null));
		Kit.log.finer("\tKey = " + key);
		Kit.log.finest("\tCost = " + cost);
	}

}
