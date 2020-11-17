/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.domains.Values.IntegerInterval;
import org.xcsp.modeler.entities.VarEntities;

import constraints.Constraint;
import heuristics.HeuristicValues;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import interfaces.ObserverBacktracking.ObserverBacktrackingUnsystematic;
import problem.Problem;
import problem.Symbolic;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import utility.Reflector;
import variables.DomainInteger.DomainRange;
import variables.DomainInteger.DomainSymbols;
import variables.DomainInteger.DomainValues;

/**
 * This class gives the description of a variable. <br>
 * A variable is attached to a problem and is uniquely identified by a number called <code>num</code>. A domain is attached to a variable and corresponds to the
 * (finite) set of values which can be assigned to it. When a value is assigned to a variable, the domain of this variable is reduced to this value. When a
 * solver tries to assign a value to a variable, it uses a <code>ValueOrderingHeuristic</code> object in order to know which value must be tried first. A
 * variable can occur in different constraints of the problem to which it is attached.
 */
public abstract class Variable implements IVar, ObserverBacktrackingUnsystematic, Comparable<Variable> {

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	public static class VariableInteger extends Variable implements IVar.Var {

		/**
		 * Builds a variable with a domain composed of all specified integer values. A range can be specified by giving an array of values composed of three
		 * int, the last one being the special value Domain.TAG_RANGE
		 */
		public VariableInteger(Problem problem, String name, int[] values) {
			super(problem, name);
			if (values.length == 1)
				this.dom = new DomainRange(this, values[0], values[0]);
			else if (values.length == 2)
				this.dom = new DomainBinary(this, values[0], values[1]);
			else if (values.length == 3 && values[2] == Domain.TAG_RANGE)
				this.dom = new DomainRange(this, values[0], values[1]);
			else
				this.dom = new DomainValues(this, values);
		}

		public VariableInteger(Problem problem, String name, IntegerInterval interval) {
			super(problem, name);
			this.dom = new DomainRange(this, Utilities.safeIntWhileHandlingInfinity(interval.inf), Utilities.safeIntWhileHandlingInfinity(interval.sup));
		}

		public VariableInteger(Problem problem, String name) {
			super(problem, name);
			this.dom = new DomainInfinite(this);
		}

		@Override
		public Object allValues() {
			return dom.allValues();
		}

	}

	public static class VariableSymbolic extends Variable implements IVar.VarSymbolic {

		/**
		 * Builds a variable with a domain composed of all specified symbolic values.
		 */
		public VariableSymbolic(Problem problem, String name, String[] symbols) {
			super(problem, name);
			if (problem.symbolic == null)
				problem.symbolic = new Symbolic();
			int[] values = problem.symbolic.manageSymbols(symbols); // values associated with symbols
			this.dom = new DomainSymbols(this, values, symbols);
		}
	}

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	@Override
	public void restoreBefore(int depth) {
		dom.restoreBefore(depth);
	}

	@Override
	public int lastModificationDepth() {
		return dom.lastRemovedLevel();
	}

	@Override
	public int compareTo(Variable x) {
		return num == UNSET_NUM && x.num == UNSET_NUM ? Integer.parseInt(id.substring(1)) - Integer.parseInt(x.id.substring(1)) : num - x.num;
	}

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static final int UNSET_NUM = -2;

	private static final int UNASSIGNED = -1;

	private static final int NB_VARIABLES_LIMIT_FOR_STORING_NEIGHBOURS = 5000;

	private static final int NB_NEIGHBOURS_LIMIT_FOR_STORING_NEIGHBOURS = 300;

	/**
	 * A special variable that can be used (for instance) by methods that requires returning three-state values: null,a variable of the problem, or this special
	 * marker.
	 */
	public static final Variable TAG = new Variable(null, null) {
	};

	public static final Comparator<Variable> decreasingDomSizeComparator = (x, y) -> Integer.compare(y.dom.size(), x.dom.size());

	public static final Comparator<Variable> decreasingStaticDegComparator = (x, y) -> Integer.compare(y.deg(), x.deg());

	public static final boolean areNumsStrictlyIncreasing(Variable... vars) {
		return IntStream.range(0, vars.length - 1).allMatch(i -> vars[i].num < vars[i + 1].num); // stronger than using compareTo
	}

	// Be aware, for a constraint scope, this method considers more that just the explicitly assigned variables
	public static final boolean areAllFixed(Variable... vars) {
		return Stream.of(vars).allMatch(x -> x.dom.size() == 1);
	}

	public static final boolean areAllDistinct(Variable... vars) {
		return IntStream.range(0, vars.length).noneMatch(i -> IntStream.range(i + 1, vars.length).anyMatch(j -> vars[i] == vars[j]));
	}

	public static final boolean areAllInitiallyBoolean(Variable... vars) {
		return Stream.of(vars).allMatch(x -> x.dom.is01());
	}

	public static final boolean haveSameDomainType(Variable... vars) {
		return IntStream.range(1, vars.length).allMatch(i -> vars[i].dom.typeIdentifier() == vars[0].dom.typeIdentifier());
	}

	public static final boolean haveSameType(Variable... vars) {
		return IntStream.range(1, vars.length).allMatch(i -> vars[i].getClass() == vars[0].getClass());
	}

	/**
	 * returns the first variable of the specified array different from the specified variable.
	 */
	public static final Variable firstDifferentVariableIn(Variable[] vars, Variable x) {
		for (Variable y : vars)
			if (y != x)
				return y;
		return null;
	}

	public static final Variable firstWipeoutVariableIn(Variable... vars) {
		for (Variable x : vars)
			if (x.dom.size() == 0)
				return x;
		return null;
	}

	public static final Variable firstNonSingletonVariableIn(Variable... vars) {
		for (Variable x : vars)
			if (x.dom.size() != 1)
				return x;
		return null;
	}

	public static final int nSingletonVariablesIn(Variable... vars) {
		int cnt = 0;
		for (Variable x : vars)
			if (x.dom.size() == 1)
				cnt++;
		return cnt;
	}

	public static final int maxInitDomSize(Variable... vars) {
		return Stream.of(vars).mapToInt(x -> x.dom.initSize()).max().getAsInt();
	}

	public static boolean isValidTuple(Variable[] vars, int[] tuple, boolean indexes) {
		assert vars.length == tuple.length;
		// System.out.println("Tuple = " + Kit.join(tuple));
		return IntStream.range(0, vars.length)
				.allMatch(i -> tuple[i] == Constants.STAR || (indexes ? vars[i].dom.isPresent(tuple[i]) : vars[i].dom.isPresentValue(tuple[i])));
	}

	public static boolean isValidTuple(Variable[] vars, String[] tuple) {
		assert vars.length == tuple.length;
		return IntStream.range(0, vars.length).allMatch(i -> ((DomainSymbols) vars[i].dom).toIdx(tuple[i]) != -1); // to control
	}

	public static int[][] filterTuples(Variable[] vars, int[][] tuples, boolean indexes) {
		return Stream.of(tuples).filter(t -> isValidTuple(vars, t, indexes)).toArray(int[][]::new);
	}

	public static String[][] filterTuples(Variable[] vars, String[][] tuples) {
		return Stream.of(tuples).filter(t -> isValidTuple(vars, t)).toArray(String[][]::new);
	}

	public static int[] filterValues(Variable x, int[] values, boolean indexes) {
		return IntStream.of(values).filter(v -> indexes ? x.dom.isPresent(v) : x.dom.isPresentValue(v)).toArray();
	}

	public static String[] filterValues(Variable x, String[] values) {
		return Stream.of(values).filter(v -> ((DomainSymbols) x.dom).toIdx(v) != -1).toArray(String[]::new);
	}

	public static final Set<Integer> setOfvaluesIn(Variable... vars) {
		Set<Integer> set = new HashSet<>();
		for (Variable x : vars)
			x.dom.execute(a -> set.add(x.dom.toVal(a)));
		return set;
	}

	public static final int nInitValuesFor(Variable... vars) {
		long l = Stream.of(vars).mapToLong(x -> x.dom.initSize()).sum();
		return Math.toIntExact(l);
	}

	public static int nValidValuesFor(Variable... vars) {
		long l = Stream.of(vars).mapToLong(x -> x.dom.size()).sum();
		return Math.toIntExact(l);
	}

	// no overflow possible because at construction time, we check that the nb of values is less than Integer.MAX_VALUE
	public static final int nRemovedValuesFor(Variable... vars) {
		return Stream.of(vars).mapToInt(x -> x.dom.nRemoved()).sum();
	}

	private static final long nTuplesFor(Variable[] vars, int ignoredVap, boolean initiSize) {
		long l = 1;
		assert firstWipeoutVariableIn(vars) == null : firstWipeoutVariableIn(vars);
		for (int i = 0; i < vars.length; i++) {
			if (i == ignoredVap)
				continue;
			int size = initiSize ? vars[i].dom.initSize() : vars[i].dom.size();
			if (l > Long.MAX_VALUE / size)
				return -1;
			l *= size;
		}
		return l;
	}

	public static final BigInteger nValidTuples(Variable[] vars, boolean initSize) {
		BigInteger prod = BigInteger.ONE;
		for (Variable x : vars)
			prod = prod.multiply(BigInteger.valueOf(initSize ? x.dom.initSize() : x.dom.size()));
		return prod;
	}

	/**
	 * @return the number of valid tuples, or Long.MAX_VALUE when this is greater than Long.MAX_VALUE, so always a positive value (or 0) is returned
	 */
	public static final long nValidTuplesBoundedAtMaxValueFor(Variable... vars) {
		long l = nTuplesFor(vars, -1, false);
		return l == -1 ? Long.MAX_VALUE : l;
	}

	/**
	 * @return the number of valid tuples, or Long.MAX_VALUE when this is greater than Long.MAX_VALUE, so always a positive value (or 0) is returned
	 */
	public static final long nValidTuplesBoundedAtMaxValueFor(Variable[] vars, int ignoredVariablePosition) {
		long l = nTuplesFor(vars, ignoredVariablePosition, false);
		return l == -1 ? Long.MAX_VALUE : l;
	}

	public static final int[] buildCumulatedSizesArray(Variable[] vars, boolean initSize) {
		int[] sizes = new int[vars.length];
		for (int i = 1; i < sizes.length; i++)
			sizes[i] = sizes[i - 1] + (initSize ? vars[i - 1].dom.initSize() : vars[i - 1].dom.size());
		return sizes;
	}

	public static class Litterals {
		private Variable[] vars;
		private boolean initSize = true;

		private Litterals(Variable[] vars) {
			this.vars = vars;
		}

		public boolean[][] booleanArray() {
			return Stream.of(vars).map(x -> new boolean[initSize ? x.dom.initSize() : x.dom.size()]).toArray(boolean[][]::new);
		}

		public short[][] shortArray() {
			return Stream.of(vars).map(x -> new short[initSize ? x.dom.initSize() : x.dom.size()]).toArray(short[][]::new);
		}

		public int[][] intArray() {
			return Stream.of(vars).map(x -> new int[initSize ? x.dom.initSize() : x.dom.size()]).toArray(int[][]::new);
		}

		public int[][] intArray(int value) {
			return Stream.of(vars).map(x -> Kit.repeat(value, initSize ? x.dom.initSize() : x.dom.size())).toArray(int[][]::new);
		}

		public long[][] longArray() {
			return Stream.of(vars).map(x -> new long[initSize ? x.dom.initSize() : x.dom.size()]).toArray(long[][]::new);
		}

		public long[][][] longArray(int thirdDimensionSize) {
			return Stream.of(vars).map(x -> new long[initSize ? x.dom.initSize() : x.dom.size()][thirdDimensionSize]).toArray(long[][][]::new);
		}

		public <E> List<E>[][] listArray() {
			return Stream.of(vars)
					.map(x -> IntStream.range(0, initSize ? x.dom.initSize() : x.dom.size()).mapToObj(i -> new ArrayList<>()).toArray(List[]::new))
					.toArray(List[][]::new);
		}

		public <T> T[][] toArray(Class<T> clazz) {
			T[][] a = Utilities.buildArray(clazz, vars.length, 0);
			for (int i = 0; i < vars.length; i++)
				a[i] = Utilities.buildArray(clazz, initSize ? vars[i].dom.initSize() : vars[i].dom.size());
			return a;
		}
	}

	public static Litterals litterals(Variable[] vars) {
		return new Litterals(vars);
	}

	public static int[][] initDomainValues(Variable[] vars) {
		return Stream.of(vars).map(x -> IntStream.range(0, x.dom.initSize()).map(a -> x.dom.toVal(a)).toArray()).toArray(int[][]::new);
	}

	public static int[][] currDomainValues(Variable[] vars) {
		return Stream.of(vars).map(x -> IntStream.range(0, x.dom.initSize()).filter(a -> x.dom.isPresent(a)).map(a -> x.dom.toVal(a)).toArray())
				.toArray(int[][]::new);
	}

	/** Arrays are not necessarily sorted. */
	public static final boolean areSimilarArrays(Variable[] vars1, Variable... vars2) {
		return vars1.length == vars2.length && Stream.of(vars1).noneMatch(x -> Stream.of(vars2).noneMatch(y -> x == y));
	}

	/**
	 * Both arrays must be increasingly sorted. Returns true iff the first set contains the second set.
	 */
	public static final boolean contains(Variable[] vars1, Variable... vars2) {
		assert areNumsStrictlyIncreasing(vars1) && areNumsStrictlyIncreasing(vars2);
		int i = 0;
		for (int j = 0; j < vars2.length; j++) {
			while (i < vars1.length && vars1[i].num < vars2[j].num)
				i++;
			if (i == vars1.length || vars1[i].num != vars2[j].num)
				return false;
		}
		return true;
	}

	public static final boolean isPermutationElligible(Variable... vars) {
		return vars[0].pb.rs.cp.settingCtrs.recognizePermutations && vars[0].dom.initSize() == vars.length && haveSameDomainType(vars);
	}

	public static final int[] domSizeArrayOf(Variable[] vars, boolean initSize) {
		return Stream.of(vars).mapToInt(x -> initSize ? x.dom.initSize() : x.dom.size()).toArray();
	}

	public static final Domain[] buildDomainsArrayFor(Variable... vars) {
		return Stream.of(vars).map(x -> x.dom).toArray(Domain[]::new);
	}

	// public static final LinkedSet[] buildElementsArrayFor(Variable... vars) {
	// return Stream.of(vars).map(x -> x.dom.set).toArray(LinkedSet[]::new);
	// }

	public static final StringBuilder signatureFor(Variable... vars) {
		StringBuilder sb = new StringBuilder();
		for (Variable x : vars)
			sb.append(x.dom.typeName()).append(' ');
		return sb;
	}

	/**
	 * Returns a string denoting the list of the (names of the) variables involved in the constraint. <br>
	 * The specified string is used as a separator between variable names. If the specified boolean is true then the default name is used.
	 */
	public static final String joinNames(Variable[] vars, String glue) {
		return Stream.of(vars).map(x -> x.id()).collect(Collectors.joining(glue));
	}

	public static final boolean areNumsNormalized(Variable... vars) {
		return IntStream.range(0, vars.length).allMatch(i -> i == vars[i].num);
	}

	public static final boolean areAllDomainsContainingValue(Variable[] vars, int v) {
		for (Variable y : vars)
			if (!y.dom.isPresentValue(v))
				return false;
		return true;
		// return Stream.of(vars).allMatch(x -> x.dom.isPresentValue(val));
	}

	public static final boolean areDomainsFull(Variable... vars) {
		return Stream.of(vars).allMatch(x -> x.dom.nRemoved() == 0);
	}

	public static final boolean areSortedDomainsIn(Variable... vars) {
		return Stream.of(vars).allMatch(x -> IntStream.range(0, x.dom.initSize() - 1).allMatch(i -> x.dom.toVal(i) < x.dom.toVal(i + 1)));
	}

	public static final boolean isInducedBy(Variable x, boolean[] presentConstraints) {
		for (Constraint c : x.ctrs)
			if (presentConstraints[c.num])
				return true;
		return false;
	}

	public static String instantiationOf(Object obj, String prefix) {
		if (obj == null)
			return "*";
		if (obj instanceof Variable)
			return ((Variable) obj).lastSolutionPrettyAssignedValue; // dom.prettyAssignedValue();
		assert obj.getClass().isArray();
		if (obj instanceof Variable[]) {
			// assert Stream.of((Variable[]) obj).noneMatch(x -> x != null && x.dom.size() != 1);
			return "[" + Stream.of((Variable[]) obj).map(x -> instantiationOf(x, null)).collect(Collectors.joining(", ")) + "]";
		} else
			return "[\n" + prefix + "  " + Stream.of((Object[]) obj).map(o -> instantiationOf(o, prefix)).collect(Collectors.joining(",\n" + prefix + "  "))
					+ "\n" + prefix + " ]";
	}

	/** Only whitespace as separator. The array only contains variables, and can be of any dimension. */
	public static String rawInstantiationOf(Object array) {
		if (array instanceof Variable[]) {
			// assert Stream.of((Variable[]) array).noneMatch(x -> x != null && x.dom.size() != 1);
			return Stream.of((Variable[]) array).map(x -> instantiationOf(x, null)).collect(Collectors.joining(" ")); // we need instantiation
																														// because of possible *; the
																														// prefix is useless
		} else // recursive call
			return Stream.of((Object[]) array).map(o -> rawInstantiationOf(o)).collect(Collectors.joining(" "));
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/** The problem to which the variable belongs. */
	public final Problem pb;

	/** The domain attached to the variable. */
	public Domain dom;

	/** The number of the variable. This is an integer between 0 and n-1, where n is the number of variables in the CN. */
	public int num = UNSET_NUM;

	/** The id (name) of the variable. */
	private String id;

	private int assignmentLevel = UNASSIGNED;

	/** This field is used during initialization in order to collect constraints where the variable is involved. */
	public final Collection<Constraint> collectedCtrs = new LinkedList<>();

	/** The set of constraints in which the variable is involved. */
	public Constraint[] ctrs;

	/**
	 * The set of variables that are neighbors to the variable. A variable x is a neighbor if both x and the variable belongs to a same scope. This array may be
	 * null if this is too space-consuming.
	 */
	public Variable[] nghs;

	/** The value ordering heuristic attached to the variable. */
	public HeuristicValues heuristicVal;

	/** Indicates if the variable can be a decision variable or not during local search. */
	// public boolean decision = true;

	/** The timestamp associated with variable. It is used for propagation. */
	public long timestamp;

	/** An object associated with the variable. Of course, may be null. The object can be used for example by an heuristic. */
	public Object data;

	public String lastSolutionPrettyAssignedValue;

	/** The weighted degree of the variable. Basically, it is equal to the sum of the weighted degree of the constraints involving it. */
	// public double wdeg;

	private Variable[] computeNeighbours(int neighborArityLimit) {
		if (ctrs.length == 0 || ctrs[ctrs.length - 1].scp.length > neighborArityLimit) // the last ctr is the one with the largest scope
			return null;
		Set<Variable> set = new TreeSet<>();
		for (Constraint c : ctrs)
			for (Variable x : c.scp)
				if (x != this) {
					set.add(x);
					if (set.size() > neighborArityLimit)
						return null;
				}
		return set.toArray(new Variable[set.size()]);
	}

	/**
	 * This method is called when the initialization is finished in order to update some data structures in relation with the constraints of the problem. This
	 * method is called by the <code>storeConstraintsToArray</code> method of the <code>Problem</code> class.
	 */
	public final void whenFinishedProblemConstruction() {
		this.ctrs = collectedCtrs.stream().sorted((c1, c2) -> c1.scp.length - c2.scp.length).toArray(Constraint[]::new);
		this.nghs = pb.variables.length > NB_VARIABLES_LIMIT_FOR_STORING_NEIGHBOURS ? null : computeNeighbours(NB_NEIGHBOURS_LIMIT_FOR_STORING_NEIGHBOURS);
	}

	/** Builds a variable with the specified id (name). */
	public Variable(Problem pb, String id) {
		this.pb = pb;
		this.id = id;
		Kit.control((id == null) == (pb == null)); // Only the variable TAG has no explicit name
	}

	public void reset() {
		assert isFuture() && dom.controlStructures(); // && Kit.control(dom.nRemoved() == 0 ??
		// if (!preserveWeightedDegrees)
		// this.resetWdeg();
		timestamp = 0;
	}

	public final String defaultId() {
		return "V" + num;
	}

	@Override
	public final String id() {
		return id;
	}

	public final String getId(boolean defaultId) {
		return defaultId ? defaultId() : id();
	}

	public final void setId(String id) {
		this.id = id;
		VarEntities.VarAlone va = pb.varEntities.varToVarAlone.get(this);
		if (va != null)
			va.id = id;
	}

	public final int assignmentLevel() {
		return assignmentLevel;
	}

	public final boolean isAssigned() {
		return assignmentLevel >= 0;
	}

	/**
	 * Determines if the variable is future, i.e., neither past (assigned) nor disconnected.
	 */
	public final boolean isFuture() {
		return assignmentLevel == UNASSIGNED;
	}

	public final void buildValueOrderingHeuristic() {
		if (heuristicVal == null) {
			String className = this.dom instanceof DomainInfinite ? First.class.getName() : pb.rs.cp.settingValh.classForValHeuristic;
			Set<Class<?>> classes = pb.rs.handlerClasses.map.get(HeuristicValues.class);
			heuristicVal = Reflector.buildObject(className, classes, this, pb.rs.cp.settingValh.anti);
		}
	}

	/**
	 * Returns the (first) binary constraint involving the variable and the given one.
	 * 
	 * @param x
	 *            a given variable
	 * @return the (first) binary constraint involving the variable and the given one if it exits and <code> null </code> otherwise.
	 */
	public final Constraint firstBinaryConstraintWith(Variable x) {
		assert this != x;
		for (Constraint c : ctrs)
			if (c.scp.length == 2 && c.involves(x))
				return c;
		return null;
	}

	/**
	 * Determines if this variable and the specified one are involved together in at least one constraint.
	 */
	public final boolean isNeighbourOf(Variable x) {
		if (nghs != null)
			return Arrays.binarySearch(nghs, x) >= 0;
		if (ctrs.length > x.ctrs.length)
			return x.isNeighbourOf(this);
		for (Constraint c : ctrs)
			if (c.involves(x))
				return true;
		return false;
	}

	/**
	 * This method is called, by a tree solver, when the given value must be assigned to the variable. <br>
	 * 
	 * @param a
	 *            the index of a value to assign to the variable
	 */
	public final void doAssignment(int a) {
		assert isFuture() && dom.isPresent(a) : isFuture() + " " + dom.isPresent(a);
		dom.reduceToElementary(a);
		assignmentLevel = pb.solver.depth(); // keep at this position
		for (Constraint c : ctrs)
			c.doPastVariable(this);
	}

	/**
	 * This method is called in order to undo the last assignment of the variable. <br>
	 */
	public final void undoAssignment() {
		assert !isFuture();
		for (Constraint c : ctrs)
			c.undoPastVariable(this);
		assignmentLevel = UNASSIGNED;
		// restoration of domains is done by the solver
	}

	/**
	 * Returns the static degree of this variable, i.e., the number of constraints in which it is involved.
	 */
	public final int deg() {
		return ctrs.length;
	}

	/**
	 * Returns the dynamic degree of this variable, i.e., the number of constraints which involves this variable and at least another future variable.
	 */
	public final int ddeg() {
		int cnt = 0;
		for (Constraint c : ctrs)
			if (c.futvars.size() >= 2)
				cnt++;
		return cnt;
	}

	public final double ddegOnDom() {
		return ddeg() / (double) dom.size();
	}

	public final double wdeg() {
		return ((WdegVariant) ((SolverBacktrack) pb.solver).heuristicVars).vscores[num];
	}

	public final double wdegOnDom() {
		return wdeg() / dom.size();
	}

	@Override
	public final String toString() {
		return id();
	}

	public final void display(boolean exhaustively) {
		Kit.log.finer("Variable " + this + " with num=" + num + ", degree=" + ctrs.length + ", " + dom.size() + " values {" + dom.stringListOfValues()
				+ "} and domain type " + dom.typeName() + " " + (this.isAssigned() ? " is assigned" : ""));
		if (exhaustively) {
			dom.display(exhaustively);
			Kit.log.finer("  ctrs = {" + Kit.join(ctrs) + "}\n  nghs = {" + Kit.join(nghs != null ? nghs : computeNeighbours(Integer.MAX_VALUE)) + "}\n");
		}
	}

}
