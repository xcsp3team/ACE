/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import static constraints.extension.structures.Table.DONT_KNOW_IF_STARRED;
import static constraints.extension.structures.Table.isStarred;
import static java.lang.reflect.Array.getLength;
import static org.xcsp.common.Constants.STAR;
import static utility.Kit.control;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.ConstraintExtension.ExtensionGeneric.ExtensionV;
import constraints.extension.STR0;
import constraints.extension.STR2;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import constraints.extension.structures.Tries;
import dashboard.Control.OptionsExtension;
import interfaces.SpecificPropagator;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNegative;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarredCompatible;
import problem.Problem;
import problem.Problem.SymmetryBreaking;
import propagation.Forward;
import propagation.Reviser;
import utility.Kit;
import utility.Reflector;
import variables.Variable;
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
	public static final class Extension1 extends ConstraintSpecific implements TagAC, TagCallCompleteFiltering {

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

		@Override
		public boolean launchFiltering(Variable x) {
			Reviser reviser = ((Forward) problem.solver.propagation).reviser;
			int nNonSingletons = 0;
			if (x.assigned() || scp.length == 1) {
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (reviser.revise(this, y) == false)
						return false;
					if (y.dom.size() > 1)
						nNonSingletons++;
				}
			} else {
				boolean revisingEventVarToo = false;
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y == x)
						continue;
					if (time < y.time)
						revisingEventVarToo = true;
					if (reviser.revise(this, y) == false)
						return false;
					if (y.dom.size() > 1)
						nNonSingletons++;
				}
				if (revisingEventVarToo && reviser.revise(this, x) == false)
					return false;
				if (x.dom.size() > 1)
					nNonSingletons++;
			}
			return nNonSingletons <= 1 ? entail() : true;
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
				assert extOptions.variantVA == 0 || extOptions.variantVA == 1 || extOptions.variantVA == 11;
				return extOptions.variantVA == 0 ? new Table(this).withSubtables() : new Tries(this, extOptions.variantVA == 11);
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
	public abstract static class ExtensionSpecific extends ConstraintExtension implements SpecificPropagator {

		public ExtensionSpecific(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		public boolean launchFiltering(Variable x) {
			return runPropagator(x);
		}
	}

	/**********************************************************************************************
	 ***** Static members
	 *********************************************************************************************/

	// private static ConstraintExtension build(Problem pb, Variable[] scp, boolean positive, boolean starred) {
	// OptionsExtension options = pb.head.control.extension;
	// control(scp.length > 1);
	// Set<Class<?>> classes = pb.head.availableClasses.get(ConstraintExtension.class);
	// String className = (positive ? options.positive : options.negative).toString();
	// className = className.equals("V") || className.equals("VA") ? "Extension" + className : className;
	//
	// boolean avoidCT = Variable.nInitValuesFor(scp) > options.domainCompactTableLimit;
	// if (scp.length > 2 && avoidCT)
	// return new STR2(pb, scp);
	//
	// if (starred) {
	// control(positive);
	// ConstraintExtension c = (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
	// control(c instanceof TagStarredCompatible, c.getClass() + " is not compatible with starred tables");
	// // currently, only STR2, STR2S, CT, CT2 and MDDSHORT
	// return c;
	// }
	// // System.out.println("hhhhh " + scp[0].dom.initSize() + " " + scp[1].dom.initSize());
	// if (scp.length == 2 && options.generic2 && scp[0].dom.initSize() * scp[1].dom.initSize() < 1_000_000) // hard coding
	// return new ExtensionV(pb, scp); // return new STR2(pb, scp);
	// if (scp.length == 2 && avoidCT)
	// return new STR2(pb, scp);
	// return (ConstraintExtension) Reflector.buildObject(className, classes, pb, scp);
	// }

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
		control(scp.length > 1, () -> " scope " + Kit.join(scp));
		control(getLength(tuples) == 0 || getLength(Array.get(tuples, 0)) == scp.length, () -> scp.length + " vs " + getLength(Array.get(tuples, 0)));

		assert Variable.areAllDistinct(scp) && Variable.haveSameType(scp);
		assert starred == DONT_KNOW_IF_STARRED || starred == isStarred(tuples);

		starred = starred == DONT_KNOW_IF_STARRED ? isStarred(tuples) : starred;
		control(!starred || positive);

		OptionsExtension options = pb.head.control.extension;
		boolean symbolic = scp[0] instanceof VariableSymbolic;

		int[][] table = symbolic ? pb.symbolic.replaceSymbols((String[][]) tuples) : (int[][]) tuples;
		if (!symbolic && !starred && options.reverse(scp.length, positive)) {
			table = Table.reverseTuples(scp, table);
			positive = !positive;
		}

		if (positive && table.length <= options.smallTableExt) // || scp.length > options.largeScopeExt);
			return STR0.buildFrom(pb, scp, table, positive, starred).storeTuplesInExtensionStructure(table, positive, starred);

		boolean avoidCT = Variable.nInitValuesFor(scp) > options.avoidingCTLimit;
		if (scp.length > 3 && avoidCT) 
			return new STR2(pb, scp).storeTuplesInExtensionStructure(table, positive, starred);

		if (!starred && table.length > options.avoidingSTRLimit) { // currently, only STR2, STR2S, CT, CT2 and CMDDS are compatible with stars
			if (scp.length == 2) {
				long nb = scp[0].dom.initSize() * scp[1].dom.initSize();
				// System.out.println(" ggggg " + nb + " " + table.length + " " + (100*table.length) + " " + (options.avoidingSTRRatio * nb));
				if (100 * table.length > options.avoidingSTRRatio * nb)
					return new ExtensionV(pb, scp).storeTuplesInExtensionStructure(table, positive, starred); // VA ?
			}
			if (scp.length == 3) { // TODO to be tested for arity 3, is it worthwhile to use V (or VA) ?
				long nb = scp[0].dom.initSize() * scp[1].dom.initSize() * scp[2].dom.initSize();
				if (100 * table.length > options.avoidingSTRRatio * nb)
					return new ExtensionV(pb, scp).storeTuplesInExtensionStructure(table, positive, starred);
			}
		}
		if (avoidCT)
			return new STR2(pb, scp).storeTuplesInExtensionStructure(table, positive, starred);

		// if (scp.length == 2 && !starred) { // currently, only STR2, STR2S, CT, CT2 and CMDDS are compatible with stars
		//// long nb = scp[0].dom.initSize() * scp[1].dom.initSize();
		//// if ()
		//
		// if (scp.length == 2 && scp[0].dom.initSize() * scp[1].dom.initSize() < 1_000_000) // hard coding
		// return new ExtensionV(pb, scp).storeTuplesInExtensionStructure(table, positive, starred); // return new STR2(pb, scp);
		// if (scp.length == 2 && avoidCT)
		// return new STR2(pb, scp).storeTuplesInExtensionStructure(table, positive, starred);
		// }

		Set<Class<?>> classes = pb.head.availableClasses.get(ConstraintExtension.class);
		String className = (positive ? options.positive : options.negative).toString();
		className = className.equals("V") || className.equals("VA") ? "Extension" + className : className;

		return ((ConstraintExtension) Reflector.buildObject(className, classes, pb, scp)).storeTuplesInExtensionStructure(table, positive, starred);

		// ConstraintExtension c = build(pb, scp, positive, starred);
		// return c.storeTuplesInExtensionStructure(table, positive, starred);
	}

	public static ConstraintExtension buildFrom(Problem pb, Variable[] scp, List<int[]> tuples, boolean positive, Boolean starred) {
		return buildFrom(pb, scp, (Object) tuples.stream().toArray(int[][]::new), positive, starred);
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
	public final ConstraintExtension storeTuplesInExtensionStructure(int[][] tuples, boolean positive, boolean starred) {
		control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), positive + " " + this.getClass().getName());
		control(!starred || this instanceof TagStarredCompatible, this.getClass() + " is not compatible with starred tables");

		// TODO be careful, we assume that the address of tuples can be used. Is that correct?
		Map<String, ExtensionStructure> map = problem.head.structureSharing.mapForExtension;
		String key = defineKey(problem.features.collecting.tableKeys.computeIfAbsent(signature() + " " + tuples + " " + positive,
				k -> "r" + problem.features.collecting.tableKeys.size()));

		// if (supporter != null) supporter).reset();

		extStructure = map.get(key);
		if (extStructure == null) {
			extStructure = buildExtensionStructure(tuples, positive);
			map.put(key, extStructure);
		} else {
			extStructure.register(this);
			assert indexesMatchValues == extStructure.firstRegisteredCtr().indexesMatchValues;
		}
		return this;
	}

	boolean controlTuples(int[][] tuples) {
		return Stream.of(tuples).allMatch(t -> IntStream.range(0, t.length).allMatch(i -> t[i] == STAR || scp[i].dom.containsValue(t[i])));
	}
}