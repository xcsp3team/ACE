/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package problem;

import static java.util.stream.Collectors.joining;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.parser.entries.XConstraints.XCtr;
import org.xcsp.parser.entries.XObjectives.XObj;

import constraints.Constraint;
import constraints.ConstraintExtension;
import constraints.ConstraintExtension.Extension1;
import constraints.ConstraintIntension;
import constraints.extension.CHybrid;
import constraints.extension.structures.MDD;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableHybrid;
import utility.Kit;
import variables.DomainFinite.DomainSpecial;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * This class stores some information (features such as sizes of domains, types of constraints, etc.) about the problem (constraint network), and ways of
 * displaying it.
 * 
 * @author Christophe Lecoutre
 */
public final class Features {

	/**********************************************************************************************
	 * Auxiliary Class Repartitioner
	 *********************************************************************************************/

	/**
	 * An object of this class allows us to record the number of occurrences of some objects (of type T).
	 */
	public final static class Repartitioner<T extends Comparable<? super T>> {

		private final static int DEFAULT_DISPLAY_LIMIT = 8;

		/**
		 * The maximum number of elements to be displayed
		 */
		private final int displayLimit;

		/**
		 * For each key, the number of occurrences is recorded (as value).
		 */
		public final TreeMap<T, Integer> repartition = new TreeMap<>();

		/**
		 * Adds an element (key) to the repartitioner. If this is the first occurrence, it is recorded with associated counter 1. Otherwise, its associated
		 * counter is incremented by 1.
		 * 
		 * @param key
		 *            the specified key to consider
		 */
		public void add(T key) {
			if (key instanceof String && ((String) key).equals(ConstraintIntension.class.getSimpleName()))
				key = (T) "Intension"; // to simplify output
			Integer nb = repartition.get(key);
			repartition.put(key, nb == null ? 1 : nb + 1);
		}

		public void remove(T key) {
			Integer nb = repartition.get(key);
			if (nb > 1)
				repartition.put(key, nb - 1);
			else
				repartition.remove(key);
		}

		public int size() {
			return repartition.size();
		}

		private Repartitioner(int displayLimit) {
			this.displayLimit = displayLimit;
		}

		public Repartitioner(boolean verbose) {
			this(verbose ? Integer.MAX_VALUE : DEFAULT_DISPLAY_LIMIT);
		}

		public Repartitioner() {
			this(DEFAULT_DISPLAY_LIMIT);
		}

		@Override
		public String toString() {
			if (repartition.size() == 0)
				return "";
			String SEP = ":", JOIN = ",";
			if (repartition.size() <= displayLimit)
				return "[" + repartition.entrySet().stream().map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN)) + "]";
			int half = DEFAULT_DISPLAY_LIMIT / 2;
			String s1 = repartition.entrySet().stream().limit(half).map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN));
			String s2 = repartition.entrySet().stream().skip(repartition.size() - (long) half).map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN));
			return "[" + s1 + "..." + s2 + "]";
		}
	}

	/**********************************************************************************************
	 * Auxiliary Class Collecting : to store (at construction time) variables and constraints (and also table keys)
	 *********************************************************************************************/

	public static final class CollectedNogood {

		public final Variable[] vars;

		public final int[] vals;

		public CollectedNogood(Variable[] scp, int[] values) {
			// is there a simpler and direct way to sort the nogood?
			assert IntStream.range(0, scp.length).allMatch(i -> scp[i].dom.containsValue(values[i]));
			boolean singleton = Stream.of(scp).anyMatch(x -> x.dom.size() == 1);
			Variable[] fscp = singleton ? Stream.of(scp).filter(x -> x.dom.size() > 1).toArray(Variable[]::new) : scp;
			int[] fvalues = singleton ? IntStream.range(0, scp.length).filter(i -> scp[i].dom.size() > 1).map(i -> values[i]).toArray() : values;

			Map<Variable, Integer> map = IntStream.range(0, fscp.length).boxed().collect(Collectors.toMap(i -> fscp[i], i -> fvalues[i]));
			map = Kit.sort(map, (e1, e2) -> e1.getKey().num - e2.getKey().num);
			this.vars = map.entrySet().stream().map(e -> e.getKey()).toArray(Variable[]::new);
			this.vals = map.entrySet().stream().mapToInt(e -> e.getValue()).toArray();
		}

		public boolean sameScopeAs(CollectedNogood cn) {
			if (vars.length != cn.vars.length)
				return false;
			for (int i = 0; i < vars.length; i++)
				if (vars[i].num != cn.vars[i].num)
					return false;
			return true;
		}

		public boolean strictSubscopeOf(CollectedNogood cn) {
			// System.out.println("uuuu0");
			if (vars.length > cn.vars.length)
				return false;
			// System.out.println("uuuu1");
			for (int i = 0, j = 0; i < vars.length; i++) {
				while (j < cn.vars.length && vars[i].num > cn.vars[j].num)
					j++;
				if (j == cn.vars.length)
					return false;
				if (vars[i].num != cn.vars[j].num)
					return false;
			}
			// System.out.println("uuuu " + this + "\n " + cn);
			return true;
		}

		public int size() {
			return vars.length;
		}

		public boolean firstValuseOf(int[] t) {
			for (int i = 0; i < vals.length; i++)
				if (vals[i] != t[i])
					return false;
			return true;
		}

		@Override
		public String toString() {
			return Kit.join(vars) + " != " + Kit.join(vals);
		}
	}

	/**
	 * This class allows us to collect variables and constraints when loading the constraint network.
	 */
	public final class Collecting {

		/**
		 * The variables that have been collected so far
		 */
		public final List<Variable> variables = new ArrayList<>();

		/**
		 * The constraints that have been collected so far
		 */
		public final List<Constraint> constraints = new ArrayList<>();

		/**
		 * The nogoods that have been collected so far
		 */
		public final List<CollectedNogood> nogoods = new ArrayList<>();

		/**
		 * The variables that have been collected so far
		 */
		public final List<VariableInteger> specialServants = new ArrayList<>();

		/**
		 * The keys used for tables, that have been collected so far, and used when storing tuples of a table constraint. Relevant only for symmetry-breaking.
		 */
		public final Map<String, String> tableKeys = new LinkedHashMap<>();

		/**
		 * Ids of discarded variables
		 */
		public final Set<String> discardedVars = new LinkedHashSet<>();

		/**
		 * The ids or numbers of variables selected by the user (if empty, no selection)
		 */
		private final Object[] selectedVars = Kit.extractFrom(problem.head.control.variables.selection);

		public int nCollectedNogoodsGathered;

		/**
		 * Returns true if the specified variable must be discarded
		 * 
		 * @param x
		 *            a variable
		 * @return true if the specified variable must be discarded
		 */
		private boolean mustDiscard(IVar x) {
			if (selectedVars.length == 0)
				return false;
			int num = collecting.variables.size() + discardedVars.size();
			boolean mustDiscard = Stream.of(selectedVars).anyMatch(o -> o.equals(num) || o.equals(x.id()));
			if (mustDiscard)
				discardedVars.add(x.id());
			return mustDiscard;
		}

		private boolean mustDiscard(IVar[] scp) {
			if (selectedVars.length == 0)
				return false;
			boolean mustDiscard = Stream.of(scp).map(x -> x.id()).anyMatch(id -> discardedVars.contains(id));
			if (mustDiscard)
				nDiscardedCtrs++;
			return mustDiscard;
		}

		/**
		 * Returns true if the specified constraint must be discarded
		 * 
		 * @param c
		 *            a constraint
		 * @return true if the specified constraint must be discarded
		 */
		public final boolean mustDiscard(XCtr c) {
			if (mustDiscard(c.vars()))
				return true;
			boolean mustDiscard = problem.head.control.constraints.ignoredType == c.type || problem.head.control.constraints.ignoreArity == c.vars().length;
			if (mustDiscard)
				nDiscardedCtrs++;
			return mustDiscard;
		}

		/**
		 * Returns true if the specified objective must be discarded
		 * 
		 * @param o
		 *            an objective
		 * @return true if the specified objective must be discarded
		 */
		public final boolean mustDiscard(XObj o) {
			return mustDiscard(o.vars());
		}

		private void printNumber(int n) {
			if (problem.head.control.general.verbose > 1) {
				int nDigits = (int) Math.log10(n) + 1;
				IntStream.range(0, nDigits).forEach(i -> System.out.print("\b")); // we need to discard previous
																					// characters
				System.out.print((n + 1) + "");
			}
		}

		/**
		 * Add the specified variable to those that have been already collected
		 * 
		 * @param x
		 *            a variable
		 * @return the num(ber) of the variable
		 */
		public int add(Variable x) {
			if (mustDiscard(x))
				return -1;
			if (variables.isEmpty()) // first call
				Kit.log.config(" " + Kit.Color.YELLOW.coloring("...Loading") + " variables");
			int num = variables.size();
			printNumber(num);
			variables.add(x);
			if (x.specialMaster != null)
				specialServants.add((VariableInteger) x);
			// domSizes.add(x.dom.initSize());
			return num;
		}

		/**
		 * Add the specified constraint to those that have been already collected
		 * 
		 * @param c
		 *            a constraint
		 * @return the num(ber) of the constraint
		 */
		public int add(Constraint c) {
			if (constraints.isEmpty()) // first call
				Kit.log.config("\n " + Kit.Color.YELLOW.coloring("...Loading") + " constraints");
			int num = constraints.size();
			printNumber(num);
			constraints.add(c);
			// int arity = c.scp.length;
			// ctrArities.add(arity);
			// ctrTypes.add(c.getClass().getSimpleName() + (arity == 1 && !(c instanceof Extension1) ? "u"
			// : (c instanceof ConstraintExtension ? "-" + c.extStructure().getClass().getSimpleName() : "")));
			// if (c.extStructure() instanceof Table)
			// tableSizes.add(((Table) c.extStructure()).tuples.length);
			// if (c instanceof CHybrid)
			// tableSizes.add(((TableHybrid) c.extStructure()).hybridTuples.length);
			return num;
		}

		public void addNogood(Variable[] vars, int[] vals) {
			nogoods.add(new CollectedNogood(vars, vals));
		}

		public void fix() {
			int i = 0;
			for (Variable x : variables) {
				x.num = i++;
				domSizes.add(x.specialMaster != null ? ((DomainSpecial) x.dom).sliceLength : x.dom.initSize());
			}
			i = 0;
			for (Constraint c : constraints) {
				c.num = i++;
				int arity = c.scp.length;
				ctrArities.add(arity);
				ctrTypes.add(c.getClass().getSimpleName() + (arity == 1 && !(c instanceof Extension1) ? "_1"
						: (c instanceof ConstraintExtension ? "-" + c.extStructure().getClass().getSimpleName() : "")));
				if (c.extStructure() instanceof Table)
					tableSizes.add(((Table) c.extStructure()).tuples.length);
				if (c instanceof CHybrid)
					tableSizes.add(((TableHybrid) c.extStructure()).hybridTuples.length);
				if (c.extStructure() instanceof MDD)
					mddSizes.add(((MDD) c.extStructure()).nNodes());
				if (c.postponable) {
					nPostponableConstraints++;
					// System.out.println(c + " " + c.getClass());
				}
			}

		}

	}

	/**********************************************************************************************
	 * Fields and methods
	 *********************************************************************************************/

	/**
	 * The problem to which this object is attached
	 */
	private final Problem problem;

	/**
	 * The object used for collecting variables and constraints at construction (initialization)
	 */
	public final Collecting collecting;

	/**
	 * Statistical repartition of variable degrees
	 */
	public final Repartitioner<Integer> varDegrees;

	/**
	 * Statistical repartition of domain sizes
	 */
	public final Repartitioner<Integer> domSizes;

	/**
	 * Statistical repartition of constraint arities
	 */
	public final Repartitioner<Integer> ctrArities;

	/**
	 * Statistical repartition of table sizes
	 */
	public final Repartitioner<Integer> tableSizes;

	/**
	 * Statistical repartition of MDD sizes
	 */
	public final Repartitioner<Integer> mddSizes;

	/**
	 * Statistical repartition of constraint types
	 */
	public final Repartitioner<String> ctrTypes;

	public int nIsolatedVars, nFixedVars, nSymbolicVars, nOmittedVars;

	public int nRemovedUnaryCtrs, nConvertedConstraints; // conversion intension to extension

	public int nMergedCtrs, nDiscardedCtrs, nAddedCtrs, nPostponableConstraints;

	/**
	 * Number of times a (generic or specific) propagator for a constraint has been effective
	 */
	public long nEffectiveFilterings;

	public int nSharedBitVectors;

	/**
	 * Number of generators, when using reinforcing techniques for posting symmetry-breaking constraints
	 */
	public int nGenerators;

	/**
	 * Number of cliques, when using reinforcing techniques for posting AllDifferent constraints
	 */
	public int nCliques;

	/**
	 * Numbers of values that have been deleted at construction time. It is computed as a sum over all variable domains.
	 */
	public int nValuesRemovedAtConstructionTime;

	/**
	 * @return the number of distinct domain types
	 */
	public int nDomTypes() {
		return (int) Stream.of(problem.variables).mapToInt(x -> x.dom.typeIdentifier()).distinct().count();
	}

	/**
	 * @return the greatest domain size
	 */
	public int maxDomSize() {
		return domSizes.repartition.lastKey();
	}

	/**
	 * @return the greatest variable degree
	 */
	public int maxVarDegree() {
		return varDegrees.repartition.lastKey();
	}

	/**
	 * @return the smallest constraint arity
	 */
	public int minCtrArity() {
		return ctrArities.repartition.firstKey();
	}

	/**
	 * @return the greatest constraint arity
	 */
	public int maxCtrArity() {
		return ctrArities.repartition.lastKey();
	}

	protected Features(Problem problem) {
		this.problem = problem;
		this.collecting = new Collecting();
		boolean verbose = problem.head.control.general.verbose > 1;
		this.varDegrees = new Repartitioner<>(verbose);
		this.domSizes = new Repartitioner<>(verbose);
		this.ctrArities = new Repartitioner<>(verbose);
		this.ctrTypes = new Repartitioner<>(true);
		this.tableSizes = new Repartitioner<>(verbose);
		this.mddSizes = new Repartitioner<>(verbose);
	}

	public boolean hasSharedExtensionStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.extStructure() != null && c.extStructure().firstRegisteredCtr() != c);
	}

	public boolean hasSharedConflictsStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.conflictsStructure != null && c.conflictsStructure.firstRegisteredCtr() != c);
	}
}
