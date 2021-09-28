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
import dashboard.Control.SettingCtrs;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import interfaces.Observers.ObserverOnConstruction;
import interfaces.SpecificPropagator;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotSymmetric;
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
 * This class allows us to represent constraints. <br>
 * A constraint is attached to a problem and is uniquely identified by a number <code>num</code> (and an identifier
 * <code>id</code>).<br>
 * A constraint involves a subset of variables of the problem.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Constraint implements ICtr, ObserverOnConstruction, Comparable<Constraint> {

	/*************************************************************************
	 ***** Implementing Interfaces
	 *************************************************************************/

	@Override
	public int compareTo(Constraint c) {
		boolean b1 = id == null, b2 = c.id == null; // b1 and b2 true iff canonical ids
		return b1 && !b2 ? -1 : !b1 && b2 ? 1 : !b1 && !b2 ? id.compareTo(c.id) : Integer.compare(num, c.num);
	}

	@Override
	public void afterProblemConstruction() {
		int n = problem.variables.length, r = scp.length;
		if (settings.positionsLb <= r && (n < settings.positionsUb || r > n / 3)) { // TODO hard coding
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
	 ***** Two very special kinds of constraints called False and True
	 *************************************************************************/

	/**
	 * A class for constraints never satisfied (to be used in very special situations)
	 */
	public static class CtrFalse extends Constraint implements SpecificPropagator, TagCallCompleteFiltering, TagAC {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return false;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			return false;
		}

		/**
		 * A message indicating the reason why such a constraint is built
		 */
		public String message;

		public CtrFalse(Problem pb, Variable[] scp, String message) {
			super(pb, scp);
			this.message = message;
		}
	}

	/**
	 * A class for constraints always satisfied (to be used in very special situations)
	 */
	public static class CtrTrue extends Constraint implements SpecificPropagator, TagCallCompleteFiltering, TagAC {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return true;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			return true;
		}

		public CtrTrue(Problem pb, Variable[] scp) {
			super(pb, scp);
		}
	}

	/*************************************************************************
	 ***** Static members
	 *************************************************************************/

	public static final int MAX_FILTERING_COMPLEXITY = 2;

	/**
	 * A special constraint that can be used (for instance) by methods that requires returning three-state values: null,
	 * a classical constraint, and this special constraint/marker.
	 */
	public static final Constraint TAG = new Constraint() {
		@Override
		public boolean isSatisfiedBy(int[] t) {
			throw new AssertionError();
		}
	};

	private static final int howManyVariablesWithin(int[] sizes, int spaceLimitation) {
		double limit = Math.pow(2, spaceLimitation);
		Arrays.sort(sizes);
		double prod = 1;
		int i = sizes.length - 1;
		for (; i >= 0 && prod <= limit; i--)
			prod = prod * sizes[i];
		return prod > limit ? (sizes.length - i - 1) : ALL;
	}

	/**
	 * Computes the greatest number k of variables such that, whatever is the selection of k variables in the specified
	 * array, the size of the Cartesian product of the domains of these variables does not exceed the specified limit.
	 * 
	 * @param vars
	 *            an array of variables
	 * @param spaceLimitation
	 *            a limit in term of number of tuples
	 * @return the greatest number of variables ensuring that the Cartesian product of the domains of the selected
	 *         variables does not exceed the specified limit
	 */
	public static final int howManyVariablesWithin(Variable[] vars, int spaceLimitation) {
		return howManyVariablesWithin(Stream.of(vars).mapToInt(x -> x.dom.size()).toArray(), spaceLimitation);
	}

	public static Constraint firstUnsatisfiedHardConstraint(Constraint[] constraints, int[] solution) {
		for (Constraint c : constraints) {
			if (c.ignored)
				continue;
			int[] t = c.tupleIterator.buffer;
			for (int i = 0; i < t.length; i++)
				t[i] = solution != null ? solution[c.scp[i].num] : c.scp[i].dom.single();
			if (c.checkIndexes(t) == false)
				return c;
		}
		return null;
	}

	public static Constraint firstUnsatisfiedHardConstraint(Constraint[] constraints) {
		return firstUnsatisfiedHardConstraint(constraints, null);
	}

	public static int nPairsOfCtrsWithSimilarScopeIn(Constraint... ctrs) {
		return IntStream.range(0, ctrs.length)
				.map(i -> (int) IntStream.range(i + 1, ctrs.length).filter(j -> Variable.areSimilarArrays(ctrs[i].scp, ctrs[j].scp)).count()).sum();
	}

	/**
	 * Returns true if the num(ber)s of the constraints in the specified array are normalized, meaning that the num(ber)
	 * of the constraint at index i of the array is i.
	 * 
	 * @param ctrs
	 *            an array of constraints
	 * @return true if the num(ber)s of the constraints in the specified array are normalized
	 */
	public static final boolean areNumsNormalized(Constraint[] ctrs) {
		return IntStream.range(0, ctrs.length).noneMatch(i -> i != ctrs[i].num);
	}

	public static final boolean isPresentScope(Constraint c, boolean[] presentVars) {
		for (Variable x : c.scp)
			if (!presentVars[x.num])
				return false;
		return true;
	}

	public static final long costOfCoveredConstraintsIn(Constraint[] ctrs) {
		// note that using streams is costly
		long cost = 0;
		for (Constraint c : ctrs)
			if (c.futvars.size() == 0)
				cost = Kit.addSafe(cost, c.costOfCurrentInstantiation());
		return cost;
	}

	public static int[][] buildTable(Constraint... ctrs) {
		Variable[] scp = Variable.scopeOf(ctrs);
		int[][] positions = Stream.of(ctrs).map(c -> IntStream.range(0, c.scp.length).map(i -> Utilities.indexOf(c.scp[i], scp)).toArray())
				.toArray(int[][]::new);
		List<int[]> list = new ArrayList<>();
		int[] values = new int[scp.length];
		EnumerationCartesian ec = new EnumerationCartesian(Variable.domSizeArrayOf(scp, true));
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
				values[i] = scp[i].dom.toVal(indexes[i]);
			list.add(values.clone()); // cloning is necessary
		}
		return Kit.intArray2D(list);
	}

	/*************************************************************************
	 * Fields
	 *************************************************************************/

	/**
	 * The problem to which the constraint belongs.
	 */
	public final Problem problem;

	/**
	 * The number of the constraint; it is <code>-1</code> when not fully initialized or not a direct constraint of the
	 * problem.
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

	public final Domain[] doms;

	/**
	 * The position of all variables of the problem in the constraint. It is -1 when not involved. For constraint of
	 * small arity, this array is not necessarily built. So, you need to call <code> positionOf </code> instead of
	 * accessing directly this field.
	 */
	private int[] positions;

	public SetDense futvars;

	/** Indicates if the constraint must be ignored. */
	public boolean ignored;

	// public int entailedLevel = -1;

	/**
	 * The key of the constraint. This field is only used for symmetry detection, when activated.
	 */
	private String key;

	/**
	 * The object that can be used to iterate over the (valid) tuples of the Cartesian product of the domains of the
	 * constraint scope.
	 */
	public final TupleIterator tupleIterator;

	protected final Supporter supporter;

	/**
	 * Indicates if for each domain of a variable involved in the constraint, the index of any value corresponds to this
	 * value.
	 */
	public final boolean indexesMatchValues;

	/**
	 * This field is used to store a tuple of (int) values. Is is inserted as a field in order to avoid overhead of
	 * memory allocations.
	 */
	protected final int[] vals;

	public int cost = 1;

	public long time;

	public int filteringComplexity;

	/**
	 * Indicates if filtering (e.g. GAC) must be controlled. If the number of uninstantiated variables is greater than
	 * this value, filtering is not achieved.
	 */
	public final int genericFilteringThreshold;

	public int nEffectiveFilterings;

	public Variable[] infiniteDomainVars;

	public SettingCtrs settings;

	/**
	 * The object that manages information about the number of conflicts of pairs (x,a) for the constraint.
	 */
	public ConflictsStructure conflictsStructure;

	/**********************************************************************************************
	 * General methods
	 *********************************************************************************************/

	public final String defaultId() {
		return "c" + num;
	}

	public final String explicitId() {
		return id;
	}

	public final String getId() {
		return id != null ? id : defaultId();
	}

	public String getKey() {
		if (key == null)
			defineKey(); // without any parameter
		return key;
	}

	public String setKey(String key) {
		control(this.key == null, "should not be called twice");
		this.key = key;
		// System.out.println("jjjjj " + key);
		return key;
	}

	/**
	 * Defines the key of the constraint from the signature, the type of the domains, and the specified data. Keys are
	 * currently used for deciding if two constraints can share some structures (this is the case when they have the
	 * same keys), and also for symmetry-breaking.
	 * 
	 * @param data
	 *            a sequence of objects that must be considered when building the key of the constraint
	 */
	protected final String defineKey(Object... data) {
		StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
		for (Object obj : data)
			sb.append('|').append(obj instanceof Collection ? Kit.join((Collection<?>) obj) : obj.getClass().isArray() ? Kit.join(obj) : obj.toString());
		return setKey(sb.toString());
	}

	/**
	 * @return the position of the variable or <code>-1</code> if the variable is not involved in the constraint
	 */
	public final int positionOf(Variable x) {
		if (positions != null)
			return positions[x.num];
		for (int i = scp.length - 1; i >= 0; i--)
			if (scp[i] == x)
				return i;
		return -1;
	}

	/** Determines if the specified variable is involved in this constraint. */
	public final boolean involves(Variable x) {
		return positionOf(x) != -1;
	}

	/** Determines if the specified variables are involved in this constraint. */
	public final boolean involves(Variable x, Variable y) {
		return positionOf(x) != -1 && positionOf(y) != -1;
	}

	public final boolean isScopeCoveredBy(Variable[] vars) {
		int cnt = 0;
		for (Variable x : vars)
			if (involves(x))
				if (++cnt == scp.length)
					return true;
		return false;
	}

	/**
	 * 
	 * @return the number of free variables (i.e., with non singleton domains) involved in the constraitn
	 */
	public final int nFreeVariables() {
		int cnt = 0;
		for (int i = futvars.limit; i >= 0; i--)
			if (scp[futvars.dense[i]].dom.size() > 1)
				cnt++;
		return cnt;
	}

	/**
	 * Returns the weighted degree of the constraint.
	 */
	public final double wdeg() {
		return ((WdegVariant) problem.solver.heuristic).cscores[num];
	}

	/**
	 * Returns true if the constraint is irreflexive. Currently, this can be only called on binary constraints, but
	 * certainly could be generalized.
	 * 
	 * @return true if the constraint is irreflexive
	 */
	public boolean isIrreflexive() {
		control(scp.length == 2);
		int[] tuple = tupleIterator.buffer;
		int p = scp[0].dom.size() > scp[1].dom.size() ? 1 : 0, q = p == 0 ? 1 : 0;
		Domain dx = scp[p].dom, dy = scp[q].dom;
		for (int a = dx.first(); a != -1; a = dx.next(a)) {
			int b = dy.toIdx(dx.toVal(a));
			if (b < 0)
				continue;
			tuple[p] = a;
			tuple[q] = b;
			if (checkIndexes(tuple))
				return false;
		}
		return true;
	}

	public boolean isSubstitutableBy(int x, int a, int b) {
		tupleIterator.firstValidTupleWith(x, a);
		return !tupleIterator.findValidTupleChecking(t -> {
			t[x] = a;
			boolean b1 = checkIndexes(t);
			t[x] = b;
			boolean b2 = checkIndexes(t);
			return b1 && !b2;
		});
	}

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

	public Boolean isSymmetric() {
		if (this instanceof TagSymmetric)
			return Boolean.TRUE;
		if (this instanceof TagNotSymmetric)
			return Boolean.FALSE;
		return null;
	}

	public int[] symmetryMatching() { // default method that can be redefined
		Boolean b = isSymmetric();
		control(b != null);
		return b ? Kit.repeat(1, scp.length) : Kit.range(1, scp.length);
	}

	/**
	 * @return true is this constraint is currently entailed
	 */
	public boolean entailed() {
		problem.solver.entail(this);
		return true;
	}

	/**
	 * Returns the intension structure (i.e., object to evaluate a Boolean expression tree) if this object is an
	 * intension constraint, null otherwise
	 * 
	 * @return the extension structure if this object is an intension constraint, or null
	 */
	public IntensionStructure intStructure() {
		return null;
	}

	/**
	 * Returns the extension structure (i.e., object like a table) if this object is an extension constraint, null
	 * otherwise
	 * 
	 * @return the extension structure if this object is an extension constraint, or null
	 */
	public ExtensionStructure extStructure() {
		return null;
	}

	public void cloneStructures(boolean onlyConflictsStructure) {
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
		this.infiniteDomainVars = new Variable[0];
		this.supporter = null;
	}

	private final int computeGenericFilteringThreshold() {
		if (this instanceof SpecificPropagator || this instanceof ConstraintExtension)
			return Integer.MAX_VALUE; // because not concerned
		int arityLimit = problem.head.control.propagation.arityLimitForGACGuaranteed;
		if (scp.length <= arityLimit)
			return Integer.MAX_VALUE;
		int futureLimitation = problem.head.control.propagation.futureLimitation;
		if (futureLimitation != -1)
			return futureLimitation < scp.length ? Math.max(arityLimit, futureLimitation) : Integer.MAX_VALUE;
		int spaceLimitation = problem.head.control.propagation.spaceLimitation;
		if (spaceLimitation != -1)
			return Math.max(arityLimit, howManyVariablesWithin(scp, spaceLimitation));
		return Integer.MAX_VALUE;
	}

	public Constraint(Problem pb, Variable[] scp) {
		this.problem = pb;
		this.scp = scp = Stream.of(scp).distinct().toArray(Variable[]::new); // this.scp and scp updated
		control(scp.length >= 1 && Stream.of(scp).allMatch(x -> x != null), () -> this + " with a scope badly formed ");
		// for (Variable x : scp) x.collectedCtrs.add(this);
		this.infiniteDomainVars = Stream.of(scp).filter(x -> x.dom instanceof DomainInfinite).toArray(Variable[]::new);

		this.doms = Variable.buildDomainsArrayFor(scp);
		this.tupleIterator = new TupleIterator(this.doms);
		this.vals = new int[scp.length];
		this.settings = pb.head.control.constraints;

		this.genericFilteringThreshold = computeGenericFilteringThreshold();
		this.indexesMatchValues = Stream.of(scp).allMatch(x -> x.dom.indexesMatchValues());

		if (this instanceof SpecificPropagator)
			pb.features.nSpecificCtrs++;
		pb.head.observersConstruction.add(this);

		this.supporter = Supporter.buildFor(this);
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
	 * Records the fact that the specified variable is not more a past variable (i.e., no more explicitly assigned by
	 * the solver)
	 * 
	 * @param x
	 *            the variable that is no more explicitly assigned
	 */
	public final void undoPastVariable(Variable x) {
		assert x.assigned() && scp[futvars.dense[futvars.size()]] == x;
		futvars.limit++;
	}

	/**
	 * Determines if the specified tuple satisfies the constraint, i.e., if the specified tuple belongs to the relation
	 * defining the constraint. Be careful: although indexes of values are managed in the core of the solver, at this
	 * stage, the given tuple contains values (and not indexes of values).
	 * 
	 * @param t
	 *            a tuple of values
	 * @return true if the specified tuple of values satisfies the constraint
	 */
	public abstract boolean isSatisfiedBy(int[] t);

	/**
	 * Determines if the specified tuple corresponds to a support of the constraint, i.e., if the tuple of values
	 * corresponding to the indexes in the specified tuple satisfies the constraint. Be careful: the given tuple must
	 * contains indexes of values.
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
	 * Returns a tuple with the indexes of the values of the current instantiation of the variables in the constraint
	 * scope
	 * 
	 * @return a tuple with the indexes of the values of the current instantiation of the variables in the constraint
	 *         scope
	 */
	private int[] instantiationIndexes() {
		int[] t = tupleIterator.buffer;
		for (int i = t.length - 1; i >= 0; i--)
			t[i] = doms[i].single();
		return t;
	}

	/**
	 * Returns true if the current instantiation of the variables of the constraint scope satisfies the constraint.
	 * IMPORTANT: all variables of the constraint scope must be fixed (i.e., with singleton domains).
	 * 
	 * @return true if the current instantiation of the variables of the constraint scope satisfies the constraint
	 */
	public boolean isSatisfiedByCurrentInstantiation() {
		return checkIndexes(instantiationIndexes());
	}

	/**
	 * Returns 0 if the constraint is satisfied by the current instantiation, or the cost that is associated with the
	 * constraint, otherwise. IMPORTANT: all variables of the constraint scope must be fixed (i.e., with singleton
	 * domains).
	 * 
	 * @return 0 if the constraint is satisfied by the current instantiation, or the cost that is associated with the
	 *         constraint
	 */
	public long costOfCurrentInstantiation() {
		return checkIndexes(instantiationIndexes()) ? 0 : cost;
	}

	/**
	 * Determines if the specified tuple of indexes (usually a support) is still valid. We have just to test that all
	 * indexes are still in the domains of the variables involved in the constraint. Do not call the
	 * <code> isSatisfiedBy </code> method instead since it does not take removed values into account.
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
	 * Seeks a support (i.e., a valid tuple satisfying the constraint) for the constraint when considering the current
	 * state of the domains and the tuple currently managed by the tuple iterator (this current tuple included in the
	 * search). A lexicographic order is used.
	 * 
	 * @return true if a support can be found from the current tuple managed by the object 'tupleIterator'
	 */
	private final boolean seekSupport() {
		return tupleIterator.findValidTupleSatisfying(this);
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order, and
	 * returns true is such a support can be found
	 * 
	 * @return true if a support can be found
	 */
	public final boolean seekFirstSupport() {
		tupleIterator.firstValidTuple();
		return seekSupport();
	}

	/**
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the
	 * requirement that the support involves the specified pair (x,a), and returns true is such a support can be found
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
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the
	 * requirement that the support involves the specified pair (x,a), and returns true is such a support can be found.
	 * The support (containing indexes of values instead of values) is recorded in the specified buffer.
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
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the
	 * requirement that the support involves the specified pairs (x,a) and (y,b), and returns true is such a support can
	 * be found. T
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
	 * Seeks a support (i.e., a valid tuple satisfying the constraint), while considering a lexicographic order and the
	 * requirement that the support must come after the current tuple (excluded) managed by the tuple iterator, and
	 * returns true is such a support can be found. Note that the current tuple (of the tuple iterator) is not
	 * necessarily valid (as it may have been deleted). Besides, if some values have been fixed in the tuple iterator,
	 * they remain fixed.
	 * 
	 * @return true if another support can be found from the current tuple (excluded) managed by the tuple iterator
	 */
	public final boolean seekNextSupport() {
		return tupleIterator.nextValidTupleCautiously() != -1 && seekSupport();
	}

	private final boolean seekConflict() {
		return tupleIterator.findValidTupleNotSatisfying(this);
	}

	/**
	 * Seeks a conflict (i.e., a valid tuple not satisfying the constraint), while considering a lexicographic order,
	 * and returns true is such a conflict can be found
	 * 
	 * @return true if a conflict can be found
	 */
	public final boolean seekFirstConflict() {
		tupleIterator.firstValidTuple();
		return seekConflict();
	}

	/**
	 * Seeks a conflict (i.e., a valid tuple not satisfying the constraint), while considering a lexicographic order and
	 * the requirement that the conflict involves the specified pair (x,a), and returns true is such a conflict can be
	 * found
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
	 * Returns the number of conflicts (i.e., valid tuples not satisfying the constraint) involving the specified pair
	 * (x,a)
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @return the number of conflicts involving the specified pair (x,a)
	 */
	public long nConflictsFor(int x, int a) {
		tupleIterator.firstValidTupleWith(x, a);
		return tupleIterator.countValidTuplesChecking(t -> !checkIndexes(t));
	}

	public boolean findArcSupportFor(int x, int a) {
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
	 * This is the method that is called for filtering. We know that the domain of the specified variable has been
	 * recently reduced, but this is not necessarily the only one in that situation.
	 */
	public final boolean filterFrom(Variable x) {
		// System.out.println("filtering " + this + " " + x + " " + this.getClass().getSimpleName());
		if (infiniteDomainVars.length > 0 && handleHugeDomains()) // Experimental (to be finished)
			return true;
		// For CSP, some conditions allow us to directly return true (because we know then that there is no filtering
		// possibility)
		if (problem.settings.framework == TypeFramework.CSP) {
			// if the condition is replaced by != TypeFramework.MACSP, there is a pb with java -ea ac
			// PlaneparkingTask.xml -ea -cm=false -ev -trace
			// possibly too with GraphColoring-sum-GraphColoring_1-fullins-3.xml.lzma
			if (futvars.size() == 0) {
				assert !isGuaranteedAC() || isSatisfiedByCurrentInstantiation() : "Unsatisfied constraint " + this + "while AC should be guaranteed";
				return isGuaranteedAC() || isSatisfiedByCurrentInstantiation();
			}
			if (futvars.size() == 1 && !x.assigned() && scp.length > 1)
				return true;
		}
		if (time > x.time && this instanceof TagCallCompleteFiltering)
			return true;
		int nBefore = problem.nValueRemovals;
		boolean consistent = this instanceof SpecificPropagator ? ((SpecificPropagator) this).runPropagator(x) : genericFiltering(x);
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
	 * Returns true if the constraint is GAC. IMPORTANT: the control is incomplete. The constraint can be currently
	 * ignored, and the test is not performed if the number of valid tuples is too large.
	 * 
	 * @return true if the constraint is GAC
	 */
	public boolean controlGAC() {
		if (ignored)
			return true;
		if (Domain.nValidTuplesBounded(doms) > 1000)
			return true;
		for (int x = 0; x < scp.length; x++)
			for (int a = doms[x].first(); a != -1; a = doms[x].next(a))
				if (seekFirstSupportWith(x, a) == false) {
					System.out.println(" " + scp[x] + "=" + doms[x].toVal(a) + " not supported by " + this);
					for (Domain dom : doms)
						dom.display(false);
					display(true);
					return false;
				}
		return true;
	}

	/**********************************************************************************************
	 * Control and display
	 *********************************************************************************************/

	public StringBuilder signature() {
		return Variable.signatureFor(scp);
	}

	@Override
	public String toString() {
		return getId() + "(" + Stream.of(scp).map(x -> x.id()).collect(Collectors.joining(",")) + ")";
	}

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
