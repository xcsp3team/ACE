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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.predicates.TreeEvaluator.ExternFunctionArity1;
import org.xcsp.common.predicates.TreeEvaluator.ExternFunctionArity2;
import org.xcsp.parser.entries.XConstraints.XCtr;
import org.xcsp.parser.entries.XObjectives.XObj;

import constraints.Constraint;
import constraints.ConstraintExtension;
import constraints.ConstraintExtension.Extension1;
import constraints.extension.CSmart;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableHybrid;
import dashboard.Output;
import variables.Variable;

/**
 * This class stores some information (features such as sizes of domains, types of constraints, etc.) about the problem
 * (constraint network), and ways of displaying it.
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
		 * Adds an element (key) to the repartitioner. If this is the first occurrence, it is recorded with associated
		 * counter 1. Otherwise, its associated counter is incremented by 1.
		 * 
		 * @param key
		 *            the specified key to consider
		 */
		public void add(T key) {
			Integer nb = repartition.get(key);
			repartition.put(key, nb == null ? 1 : nb + 1);
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
			String SEP = "#", JOIN = ",";
			if (repartition.size() <= displayLimit)
				return "[" + repartition.entrySet().stream().map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN)) + "]";
			int half = DEFAULT_DISPLAY_LIMIT / 2;
			String s1 = repartition.entrySet().stream().limit(half).map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN));
			String s2 = repartition.entrySet().stream().skip(repartition.size() - half).map(e -> e.getKey() + SEP + e.getValue()).collect(joining(JOIN));
			return "[" + s1 + "..." + s2 + "]";
		}
	}

	/**********************************************************************************************
	 * Auxiliary Class Collecting : to store (at construction time) variables and constraints (and also table keys)
	 *********************************************************************************************/

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
		 * The keys used for tables, that have been collected so far, and used when storing tuples of a table
		 * constraint. Relevant only for symmetry-breaking.
		 */
		public final Map<String, String> tableKeys = new HashMap<>();

		/**
		 * Ids of discarded variables
		 */
		public final Set<String> discardedVars = new HashSet<>();

		/**
		 * The ids or numbers of variables selected by the user (if empty, no selection)
		 */
		private final Object[] selectedVars = Variable.extractFrom(problem.head.control.variables.selection);

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
				System.out.print(Output.COMMENT_PREFIX + "Loading variables...");
			int num = variables.size();
			printNumber(num);
			variables.add(x);
			domSizes.add(x.dom.initSize());
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
				System.out.println("\n" + Output.COMMENT_PREFIX + "Loading constraints...");
			int num = constraints.size();
			printNumber(num);
			constraints.add(c);
			int arity = c.scp.length;
			ctrArities.add(arity);
			ctrTypes.add(c.getClass().getSimpleName() + (arity == 1 && !(c instanceof Extension1) ? "u"
					: (c instanceof ConstraintExtension ? "-" + c.extStructure().getClass().getSimpleName() : "")));
			if (c.extStructure() instanceof Table)
				tableSizes.add(((Table) c.extStructure()).tuples.length);
			if (c instanceof CSmart)
				tableSizes.add(((TableHybrid) c.extStructure()).hybridTuples.length);
			return num;
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
	 * Statistical repartition of constraint types
	 */
	public final Repartitioner<String> ctrTypes;

	public int nIsolatedVars, nFixedVars, nSymbolicVars;

	public int nRemovedUnaryCtrs, nConvertedConstraints; // conversion intension to extension

	public int nMergedCtrs, nDiscardedCtrs, nAddedCtrs;

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

	public ExternFunctionArity1 externFunctionArity1;
	public ExternFunctionArity2 externFunctionArity2;

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
	}

	public boolean hasSharedExtensionStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.extStructure() != null && c.extStructure().firstRegisteredCtr() != c);
	}

	public boolean hasSharedConflictsStructures() {
		return Stream.of(problem.constraints).anyMatch(c -> c.conflictsStructure != null && c.conflictsStructure.firstRegisteredCtr() != c);
	}
}
