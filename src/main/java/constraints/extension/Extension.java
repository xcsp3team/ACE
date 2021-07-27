/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Constants.STAR_SYMBOL;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.TupleManager;
import constraints.extension.Extension.ExtensionGeneric.ExtensionV;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import constraints.extension.structures.Tries;
import interfaces.FilteringSpecific;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagNegative;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagStarred;
import problem.Problem;
import propagation.Supporter.SupporterHard;
import utility.Kit;
import utility.Reflector;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

public abstract class Extension extends Constraint implements TagAC, TagFilteringCompleteAtEachCall {

	/**********************************************************************************************
	 ***** Extension1 (not a subclass of Extension)
	 *********************************************************************************************/

	// !! not a subclass of Extension
	public static final class Extension1 extends Constraint implements FilteringSpecific, TagAC, TagFilteringCompleteAtEachCall {

		@Override
		public boolean checkValues(int[] t) {
			return (Arrays.binarySearch(values, t[0]) >= 0) == positive;
		}

		final int[] values;
		final boolean positive;

		public Extension1(Problem pb, Variable x, int[] values, boolean positive) {
			super(pb, new Variable[] { x });
			assert values.length > 0 && Kit.isStrictlyIncreasing(values);
			this.values = values;
			this.positive = positive;
			this.key = signature() + " " + values + " " + positive; // TODO can we use the address of values?
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			// control(problem.solver.depth() == 0, () -> "depth: " + problem.solver.depth()); // cannot be used because after solutions, the entailed set may
			// be reset
			if (positive && scp[0].dom.removeValuesNotIn(values) == false)
				return false;
			if (!positive && scp[0].dom.removeValuesIn(values) == false)
				return false;
			assert scp[0].dom.size() > 0;
			return entailed();
		}
	}

	/**********************************************************************************************
	 ***** Generic and Global Subclasses
	 *********************************************************************************************/

	public abstract static class ExtensionGeneric extends Extension {

		public ExtensionGeneric(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

		/**
		 * Involves iterating lists of valid tuples in order to find a support.
		 */
		public static final class ExtensionV extends ExtensionGeneric {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				if (scp.length == 2)
					return Reflector.buildObject(problem.head.control.extension.classBinary, ExtensionStructure.class, this);
				if (scp.length == 3)
					return Reflector.buildObject(problem.head.control.extension.classTernary, ExtensionStructure.class, this);
				return new Table(this); // MDD(this);
			}

			public ExtensionV(Problem pb, Variable[] scp) {
				super(pb, scp);
			}
		}

		public static final class ExtensionVA extends ExtensionGeneric implements TagPositive {

			@Override
			protected ExtensionStructure buildExtensionStructure() {
				int variant = problem.head.control.extension.variant;
				assert variant == 0 || variant == 1 || variant == 11;
				return variant == 0 ? new Table(this).withSubtables() : new Tries(this, variant == 11);
			}

			public ExtensionVA(Problem pb, Variable[] scp) {
				super(pb, scp);
			}

			private final boolean seekSupportVA(int x, int a, int[] tuple, boolean another) {
				if (!another)
					tupleManager.firstValidTupleWith(x, a, tuple);
				else if (tupleManager.nextValidTupleCautiously() == -1)
					return false;
				while (true) {
					int[] t = extStructure.nextSupport(x, a, tuple);
					if (t == tuple)
						break;
					if (t == null)
						return false;
					Kit.copy(t, tuple);
					if (isValid(tuple))
						break;
					if (tupleManager.nextValidTupleCautiously() == -1)
						return false;
				}
				return true;
			}

			@Override
			public final boolean seekFirstSupportWith(int x, int a, int[] buffer) {
				buffer[x] = a;
				return seekSupportVA(x, a, buffer, false);
			}
		}
	}

	public abstract static class ExtensionGlobal extends Extension implements FilteringSpecific, ObserverBacktrackingSystematic {

		public ExtensionGlobal(Problem pb, Variable[] scp) {
			super(pb, scp);
		}
	}

	/**********************************************************************************************
	 ***** Static Methods
	 *********************************************************************************************/

	private static Extension build(Problem pb, Variable[] scp, boolean positive, boolean presentStar) {
		Kit.control(scp.length > 1);
		Set<Class<?>> classes = pb.head.handlerClasses.map.get(Extension.class);
		if (presentStar) {
			Kit.control(positive);
			String name = pb.head.control.extension.positive.toString();
			Extension c = (Extension) Reflector.buildObject(name.equals("V") || name.equals("VA") ? "Extension" + name : name, classes, pb, scp);
			Kit.control(c instanceof TagStarred); // currently, STR2, STR2S, CT, CT2 and MDDSHORT
			return c;
		}
		if (scp.length == 2 && pb.head.control.extension.validForBinary)
			return new ExtensionV(pb, scp); // return new CtrExtensionSTR2(pb, scp);
		String name = (positive ? pb.head.control.extension.positive : pb.head.control.extension.negative).toString();
		return (Extension) Reflector.buildObject(name.equals("V") || name.equals("VA") ? "Extension" + name : name, classes, pb, scp);
	}

	private static int[][] reverseTuples(Variable[] variables, int[][] tuples) {
		Kit.control(Variable.areDomainsFull(variables));
		assert Kit.isLexIncreasing(tuples);
		int cnt = 0;
		TupleManager tupleManager = new TupleManager(variables);
		int[] idxs = tupleManager.firstValidTuple(), vals = new int[idxs.length];
		List<int[]> list = new ArrayList<>();
		do {
			for (int i = vals.length - 1; i >= 0; i--)
				vals[i] = variables[i].dom.toVal(idxs[i]);
			if (cnt < tuples.length && Arrays.equals(vals, tuples[cnt]))
				cnt++;
			else
				list.add(vals.clone());
		} while (tupleManager.nextValidTuple() != -1);
		return Kit.intArray2D(list);
	}

	private static boolean isStarPresent(Object tuples) {
		return tuples instanceof int[][] ? Kit.isPresent(STAR, (int[][]) tuples) : Kit.isPresent(STAR_SYMBOL, (String[][]) tuples);
	}

	public static Constraint build(Problem pb, Variable[] scp, Object tuples, boolean positive, Boolean starred) {
		Kit.control(scp.length > 1 && Variable.haveSameType(scp));
		Kit.control(Array.getLength(tuples) == 0 || Array.getLength(Array.get(tuples, 0)) == scp.length,
				() -> "Badly formed extensional constraint " + scp.length + " " + Array.getLength(Array.get(tuples, 0)));
		if (starred == null)
			starred = isStarPresent(tuples);
		else
			assert starred == isStarPresent(tuples) : starred + " \n" + Kit.join(tuples);
		int[][] m = scp[0] instanceof VariableSymbolic ? pb.symbolic.replaceSymbols((String[][]) tuples) : (int[][]) tuples;
		if (scp[0] instanceof VariableInteger && !starred && pb.head.control.extension.mustReverse(scp.length, positive)) {
			m = reverseTuples(scp, m);
			positive = !positive;
		}
		Extension c = build(pb, scp, positive, starred);
		c.storeTuples(m, positive);
		return c;
	}

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	public ExtensionStructure extStructure;

	protected abstract ExtensionStructure buildExtensionStructure();

	@Override
	public ExtensionStructure extStructure() {
		return extStructure;
	}

	/**
	 * In this overriding, we know that we can check directly indexes with the extension structure (by construction). As a result, we cannot check values
	 * anymore (see the other method).
	 */
	@Override
	public final boolean checkIndexes(int[] t) {
		return extStructure.checkIdxs(t);
	}

	@Override
	public final boolean checkValues(int[] t) {
		return checkIndexes(toIdxs(t, tupleManager.localTuple));
	}

	@Override
	public int[] symmetryMatching() {
		return extStructure.computeVariableSymmetryMatching(this);
	}

	public Extension(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	public void cloneStructures(boolean onlyConflictsStructure) {
		super.cloneStructures(onlyConflictsStructure);
		if (!onlyConflictsStructure && extStructure.registeredCtrs().size() > 1) {
			extStructure.unregister(this);
			extStructure = Reflector.buildObject(extStructure.getClass().getSimpleName(), ExtensionStructure.class, this, extStructure);
			// IF NECESSARY, add another constructor in the class instance of ExtensionStructure
		}
	}

	public final void storeTuples(int[][] tuples, boolean positive) {
		String stuffKey = signature() + " " + tuples + " " + positive; // TODO be careful, we assume that the address of tuples can be used. Is that correct?
		this.key = problem.features.collectedTuples.computeIfAbsent(stuffKey, k -> signature() + "r" + problem.features.collectedTuples.size());

		control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), positive + " " + this.getClass().getName());
		// System.out.println("Storing tuples for " + this + " " + Kit.join(tuples) + " " + positive);

		if (supporter != null)
			((SupporterHard) supporter).reset();

		Map<String, ExtensionStructure> map = problem.head.structureSharing.mapOfExtensionStructures;
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