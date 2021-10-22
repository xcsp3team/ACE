/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package variables;

import static java.util.stream.Collectors.joining;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.domains.Values.IntegerInterval;

import constraints.Constraint;
import heuristics.HeuristicValues;
import heuristics.HeuristicVariablesDynamic.WdegVariant;
import interfaces.Observers.ObserverOnBacktracks.ObserveronBacktracksUnsystematic;
import problem.Problem;
import utility.Kit;
import variables.DomainFinite.DomainRange;
import variables.DomainFinite.DomainSymbols;
import variables.DomainFinite.DomainValues;

/**
 * A variable is attached to a problem and is uniquely identified by a number called <code>num</code>. A domain is
 * attached to a variable and corresponds to the (finite) set of values which can be assigned to it. When a value is
 * assigned to a variable, the domain of this variable is reduced to this value. When a solver tries to assign a value
 * to a variable, it uses a value ordering heuristic in order to determine which value must be tried first. A variable
 * can occur in different constraints of the problem to which it is attached.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Variable implements ObserveronBacktracksUnsystematic, Comparable<Variable>, IVar {

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * The class for integer variables
	 */
	public static final class VariableInteger extends Variable implements IVar.Var {

		/**
		 * Builds a variable with the specified id and a domain composed of all specified integer values
		 * 
		 * @param problem
		 *            the problem to which the integer variable is attached
		 * @param id
		 *            the id (name) of the variable
		 * @param values
		 *            the values in the domain of the variable
		 */
		public VariableInteger(Problem problem, String id, int[] values) {
			super(problem, id);
			assert Kit.isStrictlyIncreasing(values);
			int firstValue = values[0], lastValue = values[values.length - 1];
			if (values.length == 1)
				// TODO using DomainRange for better reasoning with ranges (when handling/combining expressions)?
				this.dom = new DomainRange(this, firstValue, firstValue);
			else if (values.length == 2)
				this.dom = new DomainBinary(this, firstValue, lastValue);
			else {
				boolean range = values.length == (lastValue - firstValue + 1);
				this.dom = range ? new DomainRange(this, firstValue, lastValue) : new DomainValues(this, values);
			}
		}

		/**
		 * Builds a variable with the specified id and a domain formed by the specified interval
		 * 
		 * @param problem
		 *            the problem to which the integer variable is attached
		 * @param id
		 *            the id (name) of the variable
		 * @param interval
		 *            the interval of values of the domain
		 */
		public VariableInteger(Problem problem, String id, IntegerInterval interval) {
			super(problem, id);
			this.dom = new DomainRange(this, Utilities.safeIntWhileHandlingInfinity(interval.inf), Utilities.safeIntWhileHandlingInfinity(interval.sup));
		}

		/**
		 * Builds a variable with the specified id and an infinite domain
		 * 
		 * @param problem
		 *            the problem to which the integer variable is attached
		 * @param id
		 *            the id (name) of the variable
		 */
		public VariableInteger(Problem problem, String id) {
			super(problem, id);
			this.dom = new DomainInfinite(this);
		}

		@Override
		public Object allValues() {
			return dom.allValues();
		}
	}

	/**
	 * The class for symbolic variables
	 */
	public static final class VariableSymbolic extends Variable implements IVar.VarSymbolic {

		/**
		 * Builds a variable with the specified id and a domain composed of all specified symbolic values
		 * 
		 * @param problem
		 *            the problem to which the symbolic variable is attached
		 * @param id
		 *            the id (name) of the variable
		 * @param symbols
		 *            the values in the domain of the variable
		 */
		public VariableSymbolic(Problem problem, String id, String[] symbols) {
			super(problem, id);
			int[] values = problem.symbolic.manageSymbols(symbols); // values associated with symbols
			this.dom = new DomainSymbols(this, values, symbols);
			problem.features.nSymbolicVars++;
		}
	}

	/**********************************************************************************************
	 * Implementing Interfaces
	 *********************************************************************************************/

	@Override
	public void restoreBefore(int depth) {
		dom.restoreBefore(depth);
	}

	@Override
	public int compareTo(Variable x) {
		return num == UNSET_NUM && x.num == UNSET_NUM ? Integer.parseInt(id.substring(1)) - Integer.parseInt(x.id.substring(1)) : num - x.num;
	}

	/**********************************************************************************************
	 * Static Members
	 *********************************************************************************************/

	public static final int UNSET_NUM = -2;

	private static final int UNASSIGNED = -1;

	private static final int NB_VARIABLES_LIMIT_FOR_STORING_NEIGHBOURS = 5000;

	private static final int NB_NEIGHBOURS_LIMIT_FOR_STORING_NEIGHBOURS = 300;

	/**
	 * A special variable that can be used (for instance) by methods that requires returning three-state values: null,a
	 * variable of the problem, or this special marker.
	 */
	public static final Variable TAG = new Variable(null, null) {
	};

	/**
	 * Returns true if the num(ber)s of the variables in the specified array are normalized, meaning that the num(ber)
	 * of the variable at index i of the array is i.
	 * 
	 * @param vars
	 *            an array of variables
	 * @return true if the num(ber)s of the variables in the specified array are normalized
	 */
	public static final boolean areNumsNormalized(Variable... vars) {
		return IntStream.range(0, vars.length).allMatch(i -> i == vars[i].num);
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return true if the specified variables are all distinct, i.e., there is two occurrences of the same variable
	 */
	public static final boolean areAllDistinct(Variable... vars) {
		return IntStream.range(0, vars.length).noneMatch(i -> IntStream.range(i + 1, vars.length).anyMatch(j -> vars[i] == vars[j]));
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return true if the specified variables have all a 0/1 domain
	 */
	public static final boolean areAllInitiallyBoolean(Variable... vars) {
		return Stream.of(vars).allMatch(x -> x.dom.is01());
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return true if the specified variables have all the same domain type
	 */
	public static final boolean haveSameDomainType(Variable... vars) {
		return IntStream.range(1, vars.length).allMatch(i -> vars[i].dom.typeIdentifier() == vars[0].dom.typeIdentifier());
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return true if the specified variables have all the same type
	 */
	public static final boolean haveSameType(Variable... vars) {
		return IntStream.range(1, vars.length).allMatch(i -> vars[i].getClass() == vars[0].getClass());
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the first variable in the specified array with an empty domain, or null
	 */
	public static final Variable firstWipeoutVariableIn(Variable... vars) {
		for (Variable x : vars)
			if (x.dom.size() == 0)
				return x;
		return null;
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the first variable in the specified array with a singleton domain, or null
	 */
	public static final Variable firstSingletonVariableIn(Variable... vars) {
		for (Variable x : vars)
			if (x.dom.size() == 1)
				return x;
		return null;
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the first variable in the specified array with a non singleton domain, or null
	 */
	public static final Variable firstNonSingletonVariableIn(Variable... vars) {
		for (Variable x : vars)
			if (x.dom.size() != 1)
				return x;
		return null;
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @param tuple
	 *            a tuple of values of value indexes
	 * @param indexes
	 *            indicates if the tuple contains values (when true) or value indexes
	 * @return true if the specified tuple is valid with respect to the specified array of variables
	 */
	public static boolean isValidTuple(Variable[] vars, int[] tuple, boolean indexes) {
		assert vars.length == tuple.length;
		return IntStream.range(0, vars.length)
				.allMatch(i -> tuple[i] == Constants.STAR || (indexes ? vars[i].dom.contains(tuple[i]) : vars[i].dom.containsValue(tuple[i])));
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the set of values contained in the domains of the specified variables
	 */
	public static final Set<Integer> setOfvaluesIn(Variable... vars) {
		Set<Integer> set = new LinkedHashSet<>();
		for (Variable x : vars)
			x.dom.execute(a -> set.add(x.dom.toVal(a)));
		return set;
	}

	// For the next 3 methods, no possible overflow because at construction time, we check that the total number of
	// values is smaller than Integer.MAX_VALUE

	/**
	 * @param vars
	 *            an array of variables
	 * @return the sum of the size of the initial domains of the specified variables
	 */
	public static final int nInitValuesFor(Variable... vars) {
		int sum = 0;
		for (Variable x : vars)
			sum += x.dom.initSize();
		return sum;
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the sum of the size of the current domains of the specified variables
	 */
	public static int nValidValuesFor(Variable... vars) {
		int sum = 0;
		for (Variable x : vars)
			sum += x.dom.size();
		return sum;
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the summed number of removed values from the current domains of the specified variables
	 */
	public static final int nRemovedValuesFor(Variable... vars) {
		int sum = 0;
		for (Variable x : vars)
			sum += x.dom.nRemoved();
		return sum;
	}

	/**
	 * A useful class for building matrices to be associated with literals, i.e., pairs (x,a) where x is a variable of
	 * the problem and a a value index in the domain of x
	 */
	public static class Litterals {

		private Variable[] vars;

		private Litterals(Variable[] vars) {
			this.vars = vars;
		}

		/**
		 * @return a matrix m with a boolean for each literal (x,a)
		 */
		public boolean[][] booleanArray() {
			return Stream.of(vars).map(x -> new boolean[x.dom.initSize()]).toArray(boolean[][]::new);
		}

		/**
		 * @return a matrix m with a short for each literal (x,a)
		 */
		public short[][] shortArray() {
			return Stream.of(vars).map(x -> new short[x.dom.initSize()]).toArray(short[][]::new);
		}

		/**
		 * @return a matrix m with an int for each literal (x,a)
		 */
		public int[][] intArray() {
			return Stream.of(vars).map(x -> new int[x.dom.initSize()]).toArray(int[][]::new);
		}

		/**
		 * @return a matrix m with a long for each literal (x,a)
		 */
		public long[][] longArray() {
			return Stream.of(vars).map(x -> new long[x.dom.initSize()]).toArray(long[][]::new);
		}

		/**
		 * @return a matrix m with a list for each literal (x,a)
		 */
		public <E> List<E>[][] listArray() {
			return Stream.of(vars).map(x -> IntStream.range(0, x.dom.initSize()).mapToObj(i -> new ArrayList<>()).toArray(List[]::new)).toArray(List[][]::new);
		}
	}

	/**
	 * Returns an object Literals, which is useful to build matrices of primitive types
	 * 
	 * @param vars
	 *            an array of variables
	 */
	public static Litterals litterals(Variable[] vars) {
		return new Litterals(vars);
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return a two-dimensional array storing for each variable, the values of its initial domain
	 */
	public static int[][] initDomainValues(Variable... vars) {
		int[][] m = new int[vars.length][];
		for (int i = 0; i < vars.length; i++) {
			Domain dom = vars[i].dom;
			if (dom instanceof DomainValues)
				m[i] = ((DomainValues) dom).values;
			else
				m[i] = IntStream.range(0, dom.initSize()).map(a -> dom.toVal(a)).toArray();
		}
		return m;
	}

	/**
	 * @param ctrs
	 *            an array of constraints
	 * 
	 * @return an array of variables with those that are successively encountered when considering the scope of the
	 *         specified constraints
	 */
	public static final Variable[] scopeOf(Constraint[] ctrs) {
		Set<Variable> set = new LinkedHashSet<>();
		for (Constraint c : ctrs)
			for (Variable x : c.scp)
				set.add(x);
		return set.stream().toArray(Variable[]::new);
	}

	/**
	 * Returns a string composed of the values assigned to the variables that are successively encountered when
	 * considering the specified object. Carriage return characters and the specified prefix can be used when listing
	 * these values, so as to show the structure of the arrays.
	 * 
	 * @param obj
	 *            an object that can be a stand-alone variable or an array (of any dimension) fo variables, or even null
	 * @param prefix
	 *            a prefix used when the specified object is an array with (at least) two dimensions
	 * @return a string corresponding to the complete instantiation of the variables that are present in the specified
	 *         object
	 */
	public static String instantiationOf(Object obj, String prefix) {
		if (obj == null)
			return "*";
		if (obj instanceof Variable) {
			Variable x = (Variable) obj;
			return x.dom.prettyValueOf(x.problem.solver.solutions.last[x.num]);
		}
		assert obj.getClass().isArray();
		if (obj instanceof Variable[]) {
			// assert Stream.of((Variable[]) obj).noneMatch(x -> x != null && x.dom.size() != 1);
			return "[" + Stream.of((Variable[]) obj).map(x -> instantiationOf(x, null)).collect(joining(", ")) + "]";
		}
		return "[\n" + prefix + "  " + Stream.of((Object[]) obj).map(o -> instantiationOf(o, prefix)).collect(joining(",\n" + prefix + "  ")) + "\n" + prefix
				+ " ]";
	}

	/**
	 * Returns a string composed of the values assigned to the variables that are successively encountered when
	 * considering the specified array. Only whitespace is used as separator, and the array only contains variables, and
	 * can be of any dimension.
	 * 
	 * @param array
	 *            an array (of any dimension) of variables
	 * @return a string corresponding to the complete instantiation of the variables that are present in the specified
	 *         array
	 */
	public static String rawInstantiationOf(Object array) {
		if (array instanceof Variable[]) {
			// we call instantiation because of possible *; the prefix is useless
			return Stream.of((Variable[]) array).map(x -> instantiationOf(x, null)).collect(joining(" "));
		}
		// recursive call
		return Stream.of((Object[]) array).map(o -> rawInstantiationOf(o)).collect(joining(" "));
	}

	/**
	 * @param vars
	 *            an array of variables
	 * @return the signature of the specified variables by considering the name of their domain types
	 */
	public static final StringBuilder signatureFor(Variable... vars) {
		StringBuilder sb = new StringBuilder();
		for (Variable x : vars)
			sb.append(x.dom.typeName()).append(' ');
		return sb;
	}

	/**
	 * Analyzes the specified string in order to extract the id or number of variables. This method is used to treat
	 * options set by the user concerning possible priority variables or partial instantiations.
	 * 
	 * @param s
	 *            a string denoting a list of variable ids and/or numbers
	 * @return an array with the ids or numbers of variables involved in the specified string
	 */
	public static Object[] extractFrom(String s) {
		if (s == null || s.trim().length() == 0)
			return new Object[0];
		Set<Object> set = new HashSet<>();
		for (String token : s.split(",")) {
			if (token.contains("..")) {
				control(token.matches("-?\\d+\\.\\.\\d+"), () -> " Pb with " + token);
				int[] t = Utilities.toIntegers(token.split("\\.\\."));
				for (int num = Math.abs(t[0]); num <= t[1]; num++)
					if (t[0] >= 0)
						set.add(num);
					else
						set.remove(num);
			} else {
				Integer num = Utilities.toInteger(token);
				if (num != null) {
					if (num >= 0)
						set.add(num);
					else
						set.remove(-num);
				} else
					set.add(token); // must be the id of a variable
			}
		}
		return set.stream().toArray();
	}

	/**********************************************************************************************
	 * Class Members
	 *********************************************************************************************/

	/**
	 * The problem to which the variable belongs
	 */
	public final Problem problem;

	/**
	 * The domain attached to the variable
	 */
	public Domain dom;

	/**
	 * The number of the variable. This is an integer between 0 and n-1, where n is the number of variables in the
	 * constraint network.
	 */
	public int num = UNSET_NUM;

	/**
	 * The id (name) of the variable
	 */
	private String id;

	/**
	 * The level where the variable has been explicitly assigned, or -1
	 */
	public int assignmentLevel = UNASSIGNED;

	/**
	 * The array of constraints involving this variable
	 */
	public Constraint[] ctrs;

	/**
	 * The set of variables that are neighbors to the variable. Two variables are neighbors if they are involved
	 * together in a constraint. This array may be null if this is too space-consuming.
	 */
	public Variable[] nghs;

	/**
	 * The value ordering heuristic attached to the variable
	 */
	public HeuristicValues heuristic;

	/**
	 * The timestamp associated with the variable. It is used during filtering/propagation.
	 */
	public long time;

	/**
	 * failed[a] gives the number of assignments that directly failed with a
	 */
	public int[] failed;

	private Variable[] computeNeighbours(int neighborArityLimit) {
		if (ctrs.length == 0 || ctrs[ctrs.length - 1].scp.length > neighborArityLimit)
			// the last constraint is the one with the largest scope
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
	 * This method is called when the initialization of the problem is finished in order to record the constraints
	 * involving this variable.
	 */
	public final void storeInvolvingConstraints(List<Constraint> constraints) {
		this.ctrs = constraints.stream().toArray(Constraint[]::new);
		assert IntStream.range(0, ctrs.length - 1).allMatch(i -> ctrs[i].scp.length <= ctrs[i + 1].scp.length);
		this.nghs = problem.variables.length > NB_VARIABLES_LIMIT_FOR_STORING_NEIGHBOURS ? null : computeNeighbours(NB_NEIGHBOURS_LIMIT_FOR_STORING_NEIGHBOURS);
		this.failed = new int[dom.initSize()];
		problem.features.varDegrees.add(deg());
	}

	/**
	 * Builds a variable for the specified problem with the specified id (name)
	 * 
	 * @param pb
	 *            the problem to which the variable is attached
	 * @param id
	 *            the id of the variable
	 */
	public Variable(Problem pb, String id) {
		this.problem = pb;
		this.id = id;
		control((id == null) == (pb == null)); // Only the variable TAG has no explicit name
	}

	public void reset() {
		assert !assigned() && dom.controlStructures(); // && control(dom.nRemoved() == 0 ??
		time = 0;
	}

	/**
	 * Returns the default id of the variable, i.e., the letter V followed by its num(ber)
	 * 
	 * @return the default id of the variable
	 */
	public final String defaultId() {
		return "V" + num;
	}

	@Override
	public final String id() {
		return id;
	}

	/**
	 * Returns true if this variable has been introduced by the solver
	 * 
	 * @return true if this variable has been introduced by the solver
	 */
	public final boolean isAuxiliaryVariableIntroducedBySolver() {
		return num >= problem.variables.length - problem.nAuxVariables;
	}

	/**
	 * Returns true if the variable is assigned (already said past, or not future), i.e., explicitly assigned by the
	 * solver
	 * 
	 * @return true if the variable is assigned
	 */
	public final boolean assigned() {
		return assignmentLevel >= 0;
	}

	/**
	 * Returns the (first) binary constraint involving the variable and the specified one
	 * 
	 * @param x
	 *            a given variable
	 * @return the (first) binary constraint involving the variable and the specified one if it exits and
	 *         <code> null </code> otherwise
	 */
	public final Constraint firstBinaryConstraintWith(Variable x) {
		assert this != x;
		for (Constraint c : ctrs)
			if (c.scp.length == 2 && c.involves(x))
				return c;
		return null;
	}

	/**
	 * Returns true if this variable belongs to the specified array
	 * 
	 * @param t
	 *            an array of variables
	 */
	public final boolean presentIn(Variable[] t) {
		for (Variable x : t)
			if (x == this)
				return true;
		return false;
	}

	/**
	 * Returns true if the variable and the specified one are involved together in at least a constraint
	 * 
	 * @param x
	 *            another variable
	 * @return true if the variable and the specified one are neighbors
	 */
	public final boolean isNeighborOf(Variable x) {
		assert this != x;
		if (nghs != null)
			return Arrays.binarySearch(nghs, x) >= 0;
		if (ctrs.length > x.ctrs.length)
			return x.isNeighborOf(this);
		for (Constraint c : ctrs)
			if (c.involves(x))
				return true;
		return false;
	}

	/**
	 * Returns the first (explicitly) assigned variable that is a neighbor of this variable. REMARK: this may be costly
	 * to call
	 * 
	 * @return the first (explicitly) assigned variable that is a neighbor of this variable.
	 */
	public final Variable firstAssignedNeighbor() {
		if (nghs != null) {
			for (Variable x : nghs)
				if (x.assigned())
					return x;
		} else {
			for (Constraint c : ctrs)
				for (Variable x : c.scp)
					if (this != x && x.assigned())
						return x;
		}
		return null;
	}

	/**
	 * Returns the distance of the variable with respect to the objective, computed as follows: 0 if directly involved
	 * in the objective, 1 if a neighbor is involved in the objective, 2 otherwise
	 * 
	 * @return the distance of the variable with respect to the objective
	 */
	public final int distanceWithObjective() {
		assert problem.optimizer != null;
		Constraint c = (Constraint) problem.optimizer.ctr;
		if (c.involves(this))
			return 0;
		for (Variable y : c.scp)
			if (this.isNeighborOf(y))
				return 1;
		return 2;
	}

	/**
	 * This method is called when the value at the specified index must be assigned to this variable
	 * 
	 * @param a
	 *            the index of a value to be assigned to the variable
	 */
	public final void assign(int a) {
		assert !assigned() && dom.contains(a) : assigned() + " " + dom.contains(a);
		dom.reduceToElementary(a);
		assignmentLevel = problem.solver.depth(); // keep at this position
		for (Constraint c : ctrs)
			c.doPastVariable(this);
	}

	/**
	 * This method is called in order to undo the last assignment of the variable
	 */
	public final void unassign() {
		assert assigned();
		for (Constraint c : ctrs)
			c.undoPastVariable(this);
		assignmentLevel = UNASSIGNED;
		// restoration of domains is done by the solver
	}

	/**
	 * Returns the static degree of this variable, i.e., the number of constraints involving it
	 * 
	 * @return the static degree of this variable
	 */
	public final int deg() {
		return ctrs.length;
	}

	/**
	 * Returns the dynamic degree of this variable, i.e., the number of constraints involving this variable and at least
	 * another future (i.e., not explicitly assigned) variable
	 * 
	 * @return the dynamic degree of this variable
	 */
	public final int ddeg() {
		int cnt = 0;
		for (Constraint c : ctrs)
			if (c.futvars.size() >= 2)
				cnt++;
		return cnt;
	}

	/**
	 * @return the ratio dynamic degree of this variable over the domain size of this variable
	 */
	public final double ddegOnDom() {
		return ddeg() / (double) dom.size();
	}

	/**
	 * @return the weighted degree of this variable
	 */
	public final double wdeg() {
		return ((WdegVariant) problem.solver.heuristic).vscores[num];
	}

	/**
	 * @return the ratio weighted degree of this variable over the domain size of this variable
	 */
	public final double wdegOnDom() {
		return wdeg() / dom.size();
	}

	@Override
	public final String toString() {
		return id();
	}

	/**
	 * Displays information about the variable
	 * 
	 * @param exhaustively
	 *            true if detailed information must be displayed
	 */
	public final void display(boolean exhaustively) {
		Kit.log.finer("Variable " + this + " with num=" + num + ", degree=" + ctrs.length + ", " + dom.size() + " values {" + dom.stringOfCurrentValues()
				+ "} and domain type " + dom.typeName() + " " + (this.assigned() ? " is assigned" : ""));
		if (exhaustively) {
			dom.display(exhaustively);
			Kit.log.finer("  ctrs = {" + Kit.join(ctrs) + "}\n  nghs = {" + Kit.join(nghs != null ? nghs : computeNeighbours(Integer.MAX_VALUE)) + "}\n");
		}
	}

}

// public final void setId(String id) {
// this.id = id;
// VarEntities.VarAlone va = problem.varEntities.varToVarAlone.get(this);
// if (va != null) va.id = id; }
