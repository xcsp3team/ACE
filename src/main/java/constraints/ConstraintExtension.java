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

import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Constants.STAR_SYMBOL;
import static utility.Kit.control;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.ConstraintExtension.ExtensionGeneric.ExtensionV;
import constraints.extension.STR0;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import constraints.extension.structures.Tries;
import dashboard.Control.OptionsExtension;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.SpecificPropagator;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNegative;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import problem.Problem.SymmetryBreaking;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.TupleIterator;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

/**
 * This is the root class for representing Extension constraints, also called table constraints. Two direct subclasses are ExtensionGeneric (for implementing AC
 * filtering à la AC3rm) and ExtensionSpecific (for implementing specific propagators).
 * 
 * @author Christophe Lecoutre
 */
public abstract class ConstraintExtension extends Constraint implements TagAC, TagCallCompleteFiltering {

	/**
	 * Various filtering algorithms for extension (table) constraints
	 */
	public static enum Extension {
		V, VA, STR0, STR1, STR2, STR3, STR1N, STR2N, CT, CMDDO, CMDDS; // , RPWC, RPWC2;
	}

	/**********************************************************************************************
	 ***** Inner classes (Extension1, ExtensionGeneric and ExtensionSpecific)
	 *********************************************************************************************/

	/**
	 * This class is is used for unary extension constraints. Typically, filtering is performed at the root node of the search tree, and the constraint becomes
	 * entailed. BE CAREFUL: this is not a subclass of ConstraintExtension.
	 */
	public static final class Extension1 extends Constraint implements SpecificPropagator, TagAC, TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return (Arrays.binarySearch(values, t[0]) >= 0) == positive;
		}

		/**
		 * The set of values authorized (if positive is true) or forbidden (if positive is false) by this unary constraint
		 */
		private final int[] values;

		/**
		 * This field indicates if values are supports (when true) or conflicts (when false)
		 */
		private final boolean positive;

		/**
		 * Builds a unary extension constraint for the specified problem, involving the specified variable, and with semantics defined from the specified values
		 * and Boolean parameter
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param x
		 *            the variable involved in the unary constraint
		 * @param values
		 *            the values defining the semantics of the constraint
		 * @param positive
		 *            if true, values are supports; otherwise values are conflicts
		 */
		public Extension1(Problem pb, Variable x, int[] values, boolean positive) {
			super(pb, new Variable[] { x });
			assert values.length > 0 && Kit.isStrictlyIncreasing(values) : "" + values.length;
			this.values = values;
			this.positive = positive;
			defineKey(values, positive);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			// control(problem.solver.depth() == 0); // note sure that it is true because after solutions, the entailed
			// set may be reset
			if (positive && scp[0].dom.removeValuesNotIn(values) == false)
				return false;
			if (!positive && scp[0].dom.removeValuesIn(values) == false)
				return false;
			return entail();
		}
	}

	/**
	 * This is the root class of generic AC filtering for extension constraints.
	 */
	public abstract static class ExtensionGeneric extends ConstraintExtension {

		/**
		 * Builds an extension constraint with a generic AC filtering
		 * 
		 * @param pb
		 *            the problem to which the constraint is attached
		 * @param scp
		 *            the scope of the constraint
		 */
		public ExtensionGeneric(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		/**
		 * This class is for extension constraints with a classical generic AC filtering (iterating over lists of valid tuples in order to find a support).
		 */
		public static final class ExtensionV extends ExtensionGeneric {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				if (scp.length == 2)
					return Reflector.buildObject(extOptions.structureClass2, ExtensionStructure.class, this);
				if (scp.length == 3)
					return Reflector.buildObject(extOptions.structureClass3, ExtensionStructure.class, this);
				return new Table(this);
			}

			public ExtensionV(Problem pb, Variable[] scp) {
				super(pb, scp);
			}
		}

		/**
		 * This class is for extension constraints with a generic AC filtering following the VA (valid-allowed) scheme (iterating over both lists of valid
		 * tuples and allowed tuples in order to find a support).
		 */
		public static final class ExtensionVA extends ExtensionGeneric implements TagPositive {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				assert extOptions.variant == 0 || extOptions.variant == 1 || extOptions.variant == 11;
				return extOptions.variant == 0 ? new Table(this).withSubtables() : new Tries(this, extOptions.variant == 11);
			}

			public ExtensionVA(Problem pb, Variable[] scp) {
				super(pb, scp);
			}

			@Override
			public final boolean seekFirstSupportWith(int x, int a, int[] buffer) {
				buffer[x] = a;
				// if (!another)
				tupleIterator.firstValidTupleWith(x, a, buffer);
				// else if (tupleIterator.nextValidTupleCautiously() == -1) return false;
				while (true) {
					int[] t = extStructure.nextSupport(x, a, buffer);
					if (t == buffer)
						break;
					if (t == null)
						return false;
					Kit.copy(t, buffer);
					if (isValid(buffer))
						break;
					if (tupleIterator.nextValidTupleCautiously() == -1)
						return false;
				}
				return true;
			}
		}
	}

	/**
	 * This is the root class of specific AC filtering for extension (table) constraints.
	 */
	public abstract static class ExtensionSpecific extends ConstraintExtension implements SpecificPropagator, ObserverOnBacktracksSystematic {

		public ExtensionSpecific(Problem pb, Variable[] scp) {
			super(pb, scp);
		}
	}

	/**********************************************************************************************
	 ***** Static members
	 *********************************************************************************************/

	private static ConstraintExtension build(Problem pb, Variable[] scp, boolean positive, boolean starred) {
		OptionsExtension options = pb.head.control.extension;
		control(scp.length > 1);
		Set<Class<?>> classes = pb.head.availableClasses.get(ConstraintExtension.class);
		String className = (positive ? options.positive : options.negative).toString();
		className = className.equals("V") || className.equals("VA") ? "Extension" + className : className;
		if (starred) {
			control(positive);
			ConstraintExtension c = (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
			control(c instanceof TagStarredCompatible, c.getClass() + " is not compatible with starred tables");
			// currently, only STR2, STR2S, CT, CT2 and MDDSHORT
			return c;
		}
		if (scp.length == 2 && options.generic2)
			return new ExtensionV(pb, scp); // return new STR2(pb, scp);
		return (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
	}

	private static int[][] reverseTuples(Variable[] scp, int[][] tuples) {
		control(Stream.of(scp).allMatch(x -> x.dom.nRemoved() == 0));
		assert Kit.isLexIncreasing(tuples);
		int cnt = 0;
		TupleIterator tupleIterator = new TupleIterator(Stream.of(scp).map(x -> x.dom).toArray(Domain[]::new));
		int[] idxs = tupleIterator.firstValidTuple(), vals = new int[idxs.length];
		List<int[]> list = new ArrayList<>();
		do {
			for (int i = vals.length - 1; i >= 0; i--)
				vals[i] = scp[i].dom.toVal(idxs[i]);
			if (cnt < tuples.length && Arrays.equals(vals, tuples[cnt]))
				cnt++;
			else
				list.add(vals.clone());
		} while (tupleIterator.nextValidTuple() != -1);
		return list.stream().toArray(int[][]::new);
	}

	public static boolean isStarred(Object tuples) {
		if (tuples instanceof int[][]) {
			for (int[] t : (int[][]) tuples)
				for (int v : t)
					if (v == STAR)
						return true;
		} else {
			for (String[] t : (String[][]) tuples)
				for (String s : t)
					if (s.equals(STAR_SYMBOL))
						return true;
		}
		return false;
	}

	/**
	 * Builds and returns an extension constraint for the specified problem, with the specified scope and the semantics defined from the specified tuples.
	 * Tuples contains symbols or integers. The specified Boolean indicates if tuples are supports or conflicts. The last parameter indicates if the tuples are
	 * starred (null when the information is not known).
	 * 
	 * @param pb
	 * @param scp
	 *            the scope of the constraint
	 * @param tuples
	 *            the tuples, either symbolic or integer, defining the semantics of the constraint
	 * @param positive
	 *            indicates if tuples are supports (when true) or conflicts (when false)
	 * @param starred
	 *            indicates if the star is present, absent, or if it is not known (null)
	 * @return an extension constraint
	 */
	public static ConstraintExtension buildFrom(Problem pb, Variable[] scp, Object tuples, boolean positive, Boolean starred) {
		assert Variable.areAllDistinct(scp);
		control(scp.length > 1 && Variable.haveSameType(scp));
		control(Array.getLength(tuples) == 0 || Array.getLength(Array.get(tuples, 0)) == scp.length,
				() -> "Badly formed extensional constraint " + scp.length + " " + Array.getLength(Array.get(tuples, 0)));
		if (starred == null)
			starred = isStarred(tuples);
		else
			assert starred == isStarred(tuples) : starred;
		int[][] m = scp[0] instanceof VariableSymbolic ? pb.symbolic.replaceSymbols((String[][]) tuples) : (int[][]) tuples;
		if (scp[0] instanceof VariableInteger && !starred && pb.head.control.extension.reverse(scp.length, positive)) {
			m = reverseTuples(scp, m);
			positive = !positive;
		}
		boolean build0 = positive && (m.length <= pb.head.control.extension.smallTableExt || scp.length > pb.head.control.extension.largeScopeExt);
		ConstraintExtension c = build0 ? STR0.buildFrom(pb, scp, m, positive, starred) : build(pb, scp, positive, starred);
		c.storeTuples(m, positive);
		return c;
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	@Override
	public final boolean isSatisfiedBy(int[] t) {
		int[] buffer = tupleIterator.buffer;
		for (int i = t.length - 1; i >= 0; i--)
			buffer[i] = doms[i].toIdx(t[i]);
		return checkIndexes(buffer);
	}

	/**
	 * In this overriding, we know that we can check directly indexes with the extension structure (by construction). As a result, we do not directly check
	 * values anymore (see the other method).
	 */
	@Override
	public final boolean checkIndexes(int[] t) {
		return extStructure.checkIndexes(t);
	}

	/**
	 * The options concerning extension constraints
	 */
	protected final OptionsExtension extOptions;

	/**
	 * The extension structure defining the semantics of the constraint
	 */
	public ExtensionStructure extStructure;

	/**
	 * Builds and returns the extension structure to be attached to this constraint. This method is sometimes used (in which case, it has to be overridden)
	 * instead of implementing it directly in the constraint constructor in order to be able to use a cache (map), and so, not systematically building a new
	 * extension structure.
	 * 
	 * @return the extension structure to be attached to this constraint
	 */
	protected ExtensionStructure buildExtensionStructure() {
		return null;
	}

	/**
	 * Builds and returns the extension structure to be attached to this constraint from the specified table and the specified Boolean
	 * 
	 * @param tuples
	 *            the tuples defining the semantics of the extension constraint
	 * @param positive
	 *            indicates if the tuples are supports or conflicts
	 * @return the extension structure to be attached to this constraint
	 */
	protected ExtensionStructure buildExtensionStructure(int[][] tuples, boolean positive) {
		ExtensionStructure es = buildExtensionStructure(); // note that the constraint is automatically registered
		control(es != null, "Maybe you have to override buildExtensionStructure()");
		es.originalTuples = this instanceof ExtensionGeneric || problem.head.control.problem.symmetryBreaking != SymmetryBreaking.NO ? tuples : null;
		es.originalPositive = positive;
		es.storeTuples(tuples, positive);
		return es;
	}

	@Override
	public ExtensionStructure extStructure() {
		return extStructure;
	}

	@Override
	public void cloneStructures(boolean onlyConflictsStructure) {
		super.cloneStructures(onlyConflictsStructure);
		if (!onlyConflictsStructure && extStructure.registeredCtrs().size() > 1) {
			extStructure.unregister(this);
			extStructure = Reflector.buildObject(extStructure.getClass().getSimpleName(), ExtensionStructure.class, this, extStructure);
		}
	}

	@Override
	public int[] symmetryMatching() {
		return extStructure.computeVariableSymmetryMatching(this);
	}

	/**
	 * Builds an extension constraint for the specified problem, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public ConstraintExtension(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.extOptions = pb.head.control.extension;
	}

	/**
	 * Records the tuples defining the semantics of the extension constraint. These tuples are inserted in the extension structure adequately, for example under
	 * the form of a matrix, a trie or an MDD.
	 * 
	 * @param tuples
	 *            the tuples defining the semantics of the extension constraint
	 * @param positive
	 *            indicates if the tuples are supports or conflicts
	 */
	public final void storeTuples(int[][] tuples, boolean positive) {
		String tableKey = signature() + " " + tuples + " " + positive;
		// TODO be careful, we assume that the address of tuples can be used. Is that correct?
		String key = defineKey(problem.features.collecting.tableKeys.computeIfAbsent(tableKey, k -> "r" + problem.features.collecting.tableKeys.size()));
		control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), positive + " " + this.getClass().getName());

		// if (supporter != null) supporter).reset();

		Map<String, ExtensionStructure> map = problem.head.structureSharing.mapForExtension;
		extStructure = map.get(key);
		if (extStructure == null) {
			extStructure = buildExtensionStructure(tuples, positive);
			map.put(key, extStructure);
		} else {
			extStructure.register(this);
			assert indexesMatchValues == extStructure.firstRegisteredCtr().indexesMatchValues;
		}
	}

	boolean controlTuples(int[][] tuples) {
		return Stream.of(tuples).allMatch(t -> IntStream.range(0, t.length).allMatch(i -> t[i] == STAR || scp[i].dom.containsValue(t[i])));
	}
}