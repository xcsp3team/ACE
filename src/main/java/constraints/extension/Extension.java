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

import constraints.ConflictsStructure;
import constraints.Constraint;
import constraints.TupleManager;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import constraints.extension.structures.TableWithSubtables;
import constraints.extension.structures.Tries;
import interfaces.FilteringSpecific;
import interfaces.Observers.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagNegative;
import interfaces.Tags.TagPositive;
import interfaces.Tags.TagShort;
import problem.Problem;
import propagation.Supporter.SupporterHard;
import utility.Kit;
import utility.Reflector;
import variables.Variable;
import variables.Variable.VariableSymbolic;

public abstract class Extension extends Constraint implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	/**********************************************************************************************
	 ***** Generic and Global Subclasses
	 *********************************************************************************************/

	/**
	 * Involves iterating lists of valid tuples in order to find a support.
	 */
	public static final class ExtensionV extends Extension {

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

	public static final class ExtensionVA extends Extension implements TagPositive {

		@Override
		protected ExtensionStructure buildExtensionStructure() {
			if (problem.head.control.extension.variant == 0)
				return new TableWithSubtables(this);
			assert problem.head.control.extension.variant == 1 || problem.head.control.extension.variant == 11;
			return new Tries(this, problem.head.control.extension.variant == 11);
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

	public abstract static class ExtensionGlobal extends Extension implements FilteringSpecific, ObserverBacktrackingSystematic {

		public ExtensionGlobal(Problem pb, Variable[] scp) {
			super(pb, scp);
		}
	}

	/**********************************************************************************************
	 ***** Static Methods
	 *********************************************************************************************/

	private static Extension build(Problem pb, Variable[] scp, boolean positive, boolean presentStar) {
		Set<Class<?>> classes = pb.head.handlerClasses.map.get(Extension.class);
		if (presentStar) {
			Kit.control(positive);
			Extension c = (Extension) Reflector.buildObject(Extension.class.getSimpleName() + pb.head.control.extension.positive, classes, pb, scp);
			Kit.control(c instanceof TagShort); // currently, STR2, STR2S, CT, CT2 and MDDSHORT
			return c;
		}
		if (scp.length == 1 || scp.length == 2 && pb.head.control.extension.validForBinary)
			return new ExtensionV(pb, scp); // return new CtrExtensionSTR2(pb, scp);
		String suffix = (positive ? pb.head.control.extension.positive : pb.head.control.extension.negative).toString();
		return (Extension) Reflector.buildObject(Extension.class.getSimpleName() + suffix, classes, pb, scp);
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

	public static Extension build(Problem pb, Variable[] scp, Object tuples, boolean positive, Boolean starred) {
		Kit.control(Variable.haveSameType(scp));
		Kit.control(Array.getLength(tuples) == 0 || Array.getLength(Array.get(tuples, 0)) == scp.length,
				() -> "Badly formed extensional constraint " + scp.length + " " + Array.getLength(tuples));
		if (starred == null)
			starred = isStarPresent(tuples);
		else
			assert starred == isStarPresent(tuples) : starred + " \n" + Kit.join(tuples);
		Extension c = build(pb, scp, positive, starred);

		int[][] m = null;
		if (scp[0] instanceof VariableSymbolic) {
			m = pb.symbolic.replaceSymbols((String[][]) tuples);
			pb.symbolic.store(c, (String[][]) tuples);
		} else {
			m = (int[][]) tuples;
			if (!starred && pb.head.control.extension.mustReverse(scp.length, positive)) {
				m = reverseTuples(scp, m);
				positive = !positive;
			}
		}

		String stuffKey = c.signature() + " " + m + " " + positive; // TODO be careful, we assume that the address of tuples can be used
		c.key = pb.features.collectedTuples.computeIfAbsent(stuffKey, k -> c.signature() + "r" + pb.features.collectedTuples.size());
		// TODO something to modify above ; don't seem to be compatible (keys)
		c.storeTuples(m, positive);
		return c;
	}

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	protected ExtensionStructure extStructure;

	protected abstract ExtensionStructure buildExtensionStructure();

	@Override
	public ExtensionStructure extStructure() {
		return extStructure;
	}

	/**
	 * In this overriding, we know that we can check directly indexes with the extension structure (by construction). As a result, we cannot check values
	 * anymore (see previous method).
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
	public int[] defineSymmetryMatching() {
		return extStructure.computeVariableSymmetryMatching();
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
			// IF NECESSARY, add another constructor in the class instance of
			// ExtensionStructure
		}
	}

	public final void storeTuples(int[][] tuples, boolean positive) {
		control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), positive + " " + this.getClass().getName());
		// System.out.println("Storing tuples for " + this + " " + Kit.join(tuples) + " " + positive);

		if (supporter != null)
			((SupporterHard) supporter).reset();
		Map<String, ExtensionStructure> map = problem.head.mapOfExtensionStructures;

		if (key == null || !map.containsKey(key)) {
			extStructure = buildExtensionStructure();
			extStructure.originalTuples = problem.head.control.problem.isSymmetryBreaking() ? tuples : null;
			extStructure.originalPositive = positive;
			extStructure.storeTuples(tuples, positive);
			if (key != null) {
				map.put(key, extStructure);
				// below, "necessary" to let this code here because tuples and positive are easily accessible
				if (problem.head.control.problem.isSymmetryBreaking()) {
					Constraint.putSymmetryMatching(key, extStructure.computeVariableSymmetryMatching(tuples, positive));
				}
			}
			if (!(this instanceof ExtensionMDDShort))
				conflictsStructure = ConflictsStructure.build(this, tuples, positive);
		} else {
			extStructure = map.get(key);
			extStructure.register(this);
			conflictsStructure = extStructure.firstRegisteredCtr().conflictsStructure;
			if (conflictsStructure != null)
				conflictsStructure.register(this);
			assert indexesMatchValues == extStructure.firstRegisteredCtr().indexesMatchValues;
		}
	}

	@Override
	public boolean removeTuple(int... idxs) {
		if (extStructure.removeTuple(idxs)) {
			if (conflictsStructure != null)
				conflictsStructure.manageRemovedTuple(idxs);
			return true;
		}
		return false;
	}

	boolean controlTuples(int[][] tuples) {
		return Stream.of(tuples).allMatch(t -> IntStream.range(0, t.length).allMatch(i -> t[i] == STAR || scp[i].dom.isPresentValue(t[i])));
	}
}