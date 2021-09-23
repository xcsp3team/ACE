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
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import constraints.extension.structures.Tries;
import dashboard.Control.SettingExtension;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.SpecificPropagator;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNegative;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import utility.Kit;
import utility.Reflector;
import variables.TupleIterator;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

/**
 * This is the root class for representing extension constraints, also called table constraints. Two direct subclasses
 * are ExtensionGeneric (for implementing AC filtering à la AC3rm) and ExtensionSpecific (for implementing specific
 * propagators).
 * 
 * @author Christophe Lecoutre
 *
 */
public abstract class ConstraintExtension extends Constraint implements TagAC, TagCallCompleteFiltering {

	/**********************************************************************************************
	 ***** Inner classes (Extension1, ExtensionGeneric and ExtensionSpecific)
	 *********************************************************************************************/

	/**
	 * This class is is used for unary extension constraints. Typically, filtering is performed at the root node of the
	 * search tree, and the constraint becomes entailed. BE CAREFUL: this is not a subclass of ConstraintExtension.
	 */
	public static final class Extension1 extends Constraint implements SpecificPropagator, TagAC, TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return (Arrays.binarySearch(values, t[0]) >= 0) == positive;
		}

		/**
		 * The set of values authorized (if positive is true) or forbidden (if positive is false) by this unary
		 * constraint
		 */
		private final int[] values;

		/**
		 * This field indicates if values are supports (when true) or conflicts (when false)
		 */
		private final boolean positive;

		/**
		 * Builds a unary extension constraint for the specified problem, involving the specified variable, and with
		 * semantics defined from the specified values and Boolean parameter
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
			assert values.length > 0 && Kit.isStrictlyIncreasing(values);
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
			return entailed();
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
		 * This class is for extension constraints with a classical generic AC filtering (iterating over lists of valid
		 * tuples in order to find a support).
		 */
		public static final class ExtensionV extends ExtensionGeneric {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				if (scp.length == 2)
					return Reflector.buildObject(esettings.structureClass2, ExtensionStructure.class, this);
				if (scp.length == 3)
					return Reflector.buildObject(esettings.structureClass3, ExtensionStructure.class, this);
				return new Table(this);
			}

			public ExtensionV(Problem pb, Variable[] scp) {
				super(pb, scp);
			}
		}

		/**
		 * This class is for extension constraints with a generic AC filtering following the VA (valid-allowed) scheme
		 * (iterating over both lists of valid tuples and allowed tuples in order to find a support).
		 */
		public static final class ExtensionVA extends ExtensionGeneric implements TagPositive {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				assert esettings.variant == 0 || esettings.variant == 1 || esettings.variant == 11;
				return esettings.variant == 0 ? new Table(this).withSubtables() : new Tries(this, esettings.variant == 11);
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
		SettingExtension settings = pb.head.control.extension;
		control(scp.length > 1);
		Set<Class<?>> classes = pb.head.availableClasses.get(ConstraintExtension.class);
		String className = (positive ? settings.positive : settings.negative).toString();
		className = className.equals("V") || className.equals("VA") ? "Extension" + className : className;
		if (starred) {
			control(positive);
			ConstraintExtension c = (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
			control(c instanceof TagStarredCompatible); // currently, STR2, STR2S, CT, CT2 and MDDSHORT
			return c;
		}
		if (scp.length == 2 && settings.validForBinary)
			return new ExtensionV(pb, scp); // return new STR2(pb, scp);
		return (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
	}

	private static int[][] reverseTuples(Variable[] scp, int[][] tuples) {
		control(Variable.areDomainsFull(scp));
		assert Kit.isLexIncreasing(tuples);
		int cnt = 0;
		TupleIterator tupleIterator = new TupleIterator(Variable.buildDomainsArrayFor(scp));
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
		return Kit.intArray2D(list);
	}

	private static boolean isStarred(Object tuples) {
		return tuples instanceof int[][] ? Kit.isPresent(STAR, (int[][]) tuples) : Kit.isPresent(STAR_SYMBOL, (String[][]) tuples);
	}

	/**
	 * Builds and returns an extension constraint for the specified problem, with the specified scope and the semantics
	 * defined from the specified tuples. Tuples contains symbols or integers. The specified Boolean indicates if tuples
	 * are supports or conflicts. The last parameter indicates if the tuples are starred (null when the information is
	 * not known).
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
		control(scp.length > 1 && Variable.haveSameType(scp));
		control(Array.getLength(tuples) == 0 || Array.getLength(Array.get(tuples, 0)) == scp.length,
				() -> "Badly formed extensional constraint " + scp.length + " " + Array.getLength(Array.get(tuples, 0)));
		if (starred == null)
			starred = isStarred(tuples);
		else
			assert starred == isStarred(tuples) : starred + " \n" + Kit.join(tuples);
		int[][] m = scp[0] instanceof VariableSymbolic ? pb.symbolic.replaceSymbols((String[][]) tuples) : (int[][]) tuples;
		if (scp[0] instanceof VariableInteger && !starred && pb.head.control.extension.mustReverse(scp.length, positive)) {
			m = reverseTuples(scp, m);
			positive = !positive;
		}
		ConstraintExtension c = build(pb, scp, positive, starred);
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
	 * In this overriding, we know that we can check directly indexes with the extension structure (by construction). As
	 * a result, we do not directly check values anymore (see the other method).
	 */
	@Override
	public final boolean checkIndexes(int[] t) {
		return extStructure.checkIndexes(t);
	}

	/**
	 * The settings related to extension constraints
	 */
	protected final SettingExtension esettings;

	/**
	 * The extension structure defining the semantics of the constraint
	 */
	protected ExtensionStructure extStructure;

	/**
	 * Builds and returns the extension structure to be attached to this constraint. This method is used instead of
	 * implementing it directly in the constraint constructor in order to be able to use a cache (map), and so, not
	 * systematically building a new extension structure.
	 * 
	 * @return the extension structure to be attached to this constraint
	 */
	protected abstract ExtensionStructure buildExtensionStructure();

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
		this.esettings = pb.head.control.extension;
	}

	/**
	 * Records the tuples defining the semantics of the extension constraint. These tuples are inserted in the extension
	 * structure adequately, for example under the form of a matrix, a trie or an MDD.
	 * 
	 * @param tuples
	 *            the tuples defining the semantics of the extension constraint
	 * @param positive
	 *            indicates if the tuples are supports or conflicts
	 */
	public final void storeTuples(int[][] tuples, boolean positive) {
		String tableKey = signature() + " " + tuples + " " + positive; // TODO be careful, we assume that the address of
																		// tuples can be used. Is that correct?
		String key = setKey(
				problem.features.collecting.tableKeys.computeIfAbsent(tableKey, k -> signature() + "r" + problem.features.collecting.tableKeys.size()));
		control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), positive + " " + this.getClass().getName());

		// if (supporter != null)
		// ((SupporterHard) supporter).reset();

		Map<String, ExtensionStructure> map = problem.head.structureSharing.mapForExtension;
		extStructure = map.get(key);
		if (extStructure == null) {
			extStructure = buildExtensionStructure(); // note that the constraint is automatically registered
			extStructure.originalTuples = this instanceof ExtensionGeneric || problem.head.control.problem.isSymmetryBreaking() ? tuples : null;
			extStructure.originalPositive = positive;
			extStructure.storeTuples(tuples, positive);
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