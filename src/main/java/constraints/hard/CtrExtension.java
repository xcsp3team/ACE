/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard;

import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Constants.STAR_SYMBOL;
import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.modeler.definitions.ICtr.ICtrExtension;

import constraints.Constraint;
import constraints.CtrHard;
import constraints.TupleManager;
import constraints.hard.extension.CtrExtensionCT;
import constraints.hard.extension.CtrExtensionCT2;
import constraints.hard.extension.CtrExtensionMDD;
import constraints.hard.extension.CtrExtensionMDDShort;
import constraints.hard.extension.CtrExtensionSTR2;
import constraints.hard.extension.CtrExtensionSTR2S;
import constraints.hard.extension.CtrExtensionV;
import constraints.hard.extension.structures.Bits;
import constraints.hard.extension.structures.ExtensionStructure;
import constraints.hard.extension.structures.ExtensionStructureHard;
import executables.Resolution;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagNegative;
import interfaces.TagPositive;
import problem.Problem;
import propagation.structures.supporters.SupporterHard;
import utility.Enums.EExtension;
import utility.Kit;
import utility.Reflector;
import utility.exceptions.MissingImplementationException;
import variables.Variable;
import variables.VariableInteger;
import variables.VariableSymbolic;

public abstract class CtrExtension extends CtrHard implements TagGACGuaranteed, TagFilteringCompleteAtEachCall, ICtrExtension {

	/**********************************************************************************************
	 ***** Static
	 *********************************************************************************************/

	private static Constraint build(Problem pb, Variable[] scp, boolean positive, boolean presentStar) {
		if (presentStar) {
			if (pb.rs.cp.settingExtension.positive == EExtension.MDD)
				return new CtrExtensionMDD(pb, scp);
			if (pb.rs.cp.settingExtension.positive == EExtension.MDDSHORT)
				return new CtrExtensionMDDShort(pb, scp);
			if (pb.rs.cp.settingExtension.positive == EExtension.STR2)
				return new CtrExtensionSTR2(pb, scp);
			if (pb.rs.cp.settingExtension.positive == EExtension.STR2S)
				return new CtrExtensionSTR2S(pb, scp);
			if (pb.rs.cp.settingExtension.positive == EExtension.CT)
				return new CtrExtensionCT(pb, scp);
			if (pb.rs.cp.settingExtension.positive == EExtension.CT2)
				return new CtrExtensionCT2(pb, scp);
			// if (pb.rs.cp.extension.positive == EExtension.VA)
			// return new CtrExtensionVA(pb, scp);
			throw new IllegalArgumentException("Unimplemented table constraint for short tables");
		}
		if (scp.length == 1 || scp.length == 2 && pb.rs.cp.settingExtension.validForBinary)
			// return new CtrExtensionSTR2(pb, scp);
			return new CtrExtensionV(pb, scp); // for example for maxCSP ?
		String suffix = (positive ? pb.rs.cp.settingExtension.positive : pb.rs.cp.settingExtension.negative).toString();
		return Reflector.buildObject(CtrExtension.class.getSimpleName() + suffix, CtrExtension.class, pb, scp);
	}

	private static int[][] reverseTuples(Variable[] variables, int[][] tuples) {
		Kit.control(Variable.areDomainsFull(variables));
		assert Kit.isLexIncreasing(tuples);
		int cnt = 0;
		TupleManager tupleManager = new TupleManager(Variable.buildDomainsArrayFor(variables));
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

	public static CtrExtension build(Problem pb, Variable[] scp, Object tuples, boolean positive, Boolean starred) {
		Kit.control(Stream.of(scp).allMatch(x -> x instanceof VariableInteger) || Stream.of(scp).allMatch(x -> x instanceof VariableSymbolic));
		Kit.control(Array.getLength(tuples) == 0 || Array.getLength(Array.get(tuples, 0)) == scp.length,
				() -> "Badly formed extensional constraint " + scp.length + " " + Array.getLength(tuples));
		assert starred == null || (starred == Boolean.TRUE) == isStarPresent(tuples) : starred + " \n" + Kit.join(tuples);
		starred = starred != null ? starred : isStarPresent(tuples);

		int[][] ts = scp[0] instanceof VariableInteger ? (int[][]) tuples : pb.symbolic.replaceSymbols((String[][]) tuples);
		if (scp[0] instanceof VariableInteger && !starred)
			if ((!positive && scp.length <= pb.rs.cp.settingExtension.arityLimitForSwitchingToPositive)
					|| (positive && scp.length <= pb.rs.cp.settingExtension.arityLimitForSwitchingToNegative)) {
				ts = reverseTuples(scp, ts);
				positive = !positive;
			}
		CtrExtension c = (CtrExtension) build(pb, scp, positive, starred);
		String stuffKey = c.signature() + " " + ts + " " + positive; // TDODO be careful, we assume that the address of tuples can be used
		c.key = pb.stuff.collectedTuples.computeIfAbsent(stuffKey, k -> c.signature() + "r" + pb.stuff.collectedTuples.size());
		// TODO something tomodify above ; don't seem to be compatible (keys)
		c.storeTuples(ts, positive);
		if (scp[0] instanceof VariableSymbolic)
			pb.symbolic.store(c, (String[][]) tuples);
		return c;
	}

	// public static CtrExtension build(Problem pb, Variable[] scp, int[][] tuples, boolean positive, Boolean starred) {
	// Kit.control(tuples.length == 0 || tuples[0].length == scp.length, () -> "Badly formed extensional constraint");
	// assert starred == null || (starred == Boolean.TRUE && Kit.isPresent(Table.STAR, tuples))
	// || (starred == Boolean.FALSE && !Kit.isPresent(Table.STAR, tuples)) : starred + " " + Kit.join(scp) + "\n" + Kit.join(tuples);
	// starred = starred == null ? Kit.isPresent(Table.STAR, tuples) : starred;
	// if ((!positive && scp.length <= pb.resolution.cp.arityLimitForSwitchingToPositive)
	// || (positive && scp.length <= pb.resolution.cp.arityLimitForSwitchingToNegative)) {
	// Kit.control(!starred);
	// tuples = reverseTuples(scp, tuples);
	// positive = !positive;
	// }
	// CtrExtension constraint = (CtrExtension) build(pb, scp, positive, starred);
	// String stuffKey = constraint.signature() + " " + tuples + " " + positive; // TDODO be careful, we assume that the address of tuples
	// can be used
	// String stuffValue = pb.stuff.collectedTuples.get(stuffKey);
	// if (stuffValue != null)
	// constraint.key = stuffValue;
	// else
	// pb.stuff.collectedTuples.put(stuffKey, constraint.key = constraint.signature() + "r" + pb.stuff.collectedTuples.size());
	// constraint.storeTuples(tuples, positive);
	// return constraint;
	// }

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	protected ExtensionStructureHard extStructure;

	@Override
	public ExtensionStructureHard extStructure() {
		return extStructure;
	}

	protected abstract ExtensionStructureHard buildExtensionStructure();

	@Override
	public void cloneStructures(boolean onlyConflictsStructure) {
		super.cloneStructures(onlyConflictsStructure);
		if (!onlyConflictsStructure && extStructure.registeredCtrs().size() > 1) {
			extStructure.unregister(this);
			extStructure = Reflector.buildObject(extStructure.getClass().getSimpleName(), ExtensionStructureHard.class, this, extStructure);
			// IF NECESSARY, add another constructor in the class instance of
			// ExtensionStructure
		}
	}

	// These additional fields are typically not shared (except for a redundant
	// field that represents an overriding of the field 'extensionStructure' --
	// this is interesting for avoiding casting)
	protected void initSpecificStructures() {}

	public final void storeTuples(int[][] tuples, boolean positive) {
		Kit.control((positive && this instanceof TagPositive) || (!positive && this instanceof TagNegative)
				|| (!(this instanceof TagPositive) && !(this instanceof TagNegative)), () -> positive + " " + this.getClass().getName());
		// System.out.println("Storing tuples for " + this + " " + Kit.join(tuples) + " " + positive);

		if (supporter != null)
			((SupporterHard) supporter).reset();
		Map<String, ExtensionStructure> map = pb.rs.mapOfExtensionStructures;

		if (key == null || !map.containsKey(key)) {
			extStructure = buildExtensionStructure();
			extStructure.originalTuples = pb.rs.cp.settingProblem.isSymmetryBreaking() ? tuples : null;
			extStructure.originalPositive = positive;
			extStructure.storeTuples(tuples, positive);
			if (key != null) {
				map.put(key, extStructure);
				// below, "necessary" to let this code here because tuples and positive are easily accessible
				if (pb.rs.cp.settingProblem.isSymmetryBreaking()) {
					Constraint.putSymmetryMatching(key, extStructure.computeVariableSymmetryMatching(tuples, positive));
				}
			}
			if (!(this instanceof CtrExtensionMDDShort))
				conflictsStructure = ConflictsStructure.build(this, tuples, positive);
		} else {
			extStructure = (ExtensionStructureHard) map.get(key);
			extStructure.register(this);
			conflictsStructure = extStructure.firstRegisteredCtr().conflictsStructure();
			if (conflictsStructure != null)
				conflictsStructure.register(this);
			assert indexesMatchValues == extStructure.firstRegisteredCtr().indexesMatchValues;
		}
		initSpecificStructures();
	}

	@SuppressWarnings("unused")
	private String searchSimilarBits(Bits bits) {
		Resolution resolution = pb.rs;
		for (String key : resolution.mapOfExtensionStructures.keySet()) {
			ExtensionStructure es = resolution.mapOfExtensionStructures.get(key);
			if (!(es instanceof Bits))
				continue;
			if (scp[0].dom.typeIdentifier() != bits.firstRegisteredCtr().scp[0].dom.typeIdentifier())
				continue;
			if (scp[1].dom.typeIdentifier() != bits.firstRegisteredCtr().scp[1].dom.typeIdentifier())
				continue;
			if (bits.hasSameSupportsThan((Bits) es))
				return es.firstRegisteredCtr().key;
		}
		return null;
	}

	@Override
	public int[] defineSymmetryMatching() {
		// above because necessarily from a predicate
		return extStructure.computeVariableSymmetryMatching();
	}

	// public Constraint storeTuples(String[] canonicalPredicate) {
	// assert scp.length == 2;
	// this.key = signature().append(new CanonicalExpressionParser(scp, canonicalPredicate).getKey()).toString();
	// // System.out.println("key = " + key + " " + Toolkit.buildStringFromTokens(canonicalPredicate));
	// Resolution resolution = pb.resolution;
	//
	// boolean firstOccurrenceOfKey = !resolution.mapOfExtensionStructures.containsKey(key);
	// String equivalentKeyMet = null;
	// if (firstOccurrenceOfKey) {
	// extensionStructure = new Bits(this);
	// conflictsStructure = new ConflictsStructure(this);
	// ((Bits) extensionStructure).storeTuplesAndUpdateConflictsStructure(canonicalPredicate);
	// // structures of conflictStructures updated
	// // ((Bits) extensionStructure).fixSymmetric();
	//
	// equivalentKeyMet = searchSimilarBits((Bits) extensionStructure);
	// if (equivalentKeyMet == null) {
	// resolution.mapOfExtensionStructures.put(key, extensionStructure);
	// } else
	// key = equivalentKeyMet;
	// }
	// if (!firstOccurrenceOfKey || equivalentKeyMet != null) {
	// extensionStructure = (ExtensionStructureHard) resolution.mapOfExtensionStructures.get(key);
	// extensionStructure.addDependentCtr(this);
	// conflictsStructure = extensionStructure.getFirstDependentCtr().getConflictsStructure();
	// conflictsStructure.getExploitingConstraints().add(this);
	// assert areIdxsEqualToVals == extensionStructure.getFirstDependentCtr().areIdxsEqualToVals;
	// }
	// initializeAdditionalFieldsUsedWithExtensionStructure();
	// return this;
	// }

	public CtrExtension(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	public final boolean checkValues(int[] t) {
		return checkIndexes(toIdxs(t, tupleManager.localTuple));
	}

	/**
	 * In this overriding, we know that we can check directly indexes with the extension structure (by construction). As a result, we cannot check
	 * values anymore (see previous method).
	 */
	@Override
	public final boolean checkIndexes(int[] t) {
		pb.stuff.nCcks++;
		return extStructure.checkIdxs(t);
	}

	// private void updateBitsFrom(XNodeParent<? extends IVarInteger> tree) {
	// Kit.control(scp.length == 2);
	// this.id = id == null ? null : id + "_modified";
	// this.key += " " + Kit.join(tree.canonicalForm(new ArrayList<>(), tree.vars()).toArray(new String[0]));
	// extStructure.removeDependentCtr(this);
	// if (conflictsStructure != null) {
	// conflictsStructure.getExploitingConstraints().remove(this);
	// conflictsStructure = new ConflictsStructure(conflictsStructure, this);
	// }
	// Map<String, ExtensionStructure> mapOfExtensionStructures = pb.resolution.mapOfExtensionStructures;
	// if (!mapOfExtensionStructures.containsKey(key)) {
	// extStructure = new Bits(this, (Bits) extStructure);
	// EvaluationManager evaluationManager = new EvaluationManager(tree); // Symbolic.replaceSymbols(pb.symbolic,
	// universalFragmentPredicateExpression));
	// int cnt = 0;
	// Domain dom0 = scp[0].dom, dom1 = scp[1].dom;
	// int[] tmpOfValues = tupleManager.localTuple, tmpOfIndexes = new int[2];
	// for (int idx0 = 0; idx0 < dom0.initSize(); idx0++) {
	// tmpOfValues[0] = dom0.toVal(idx0);
	// tmpOfIndexes[0] = idx0;
	// for (int idx1 = 0; idx1 < dom1.initSize(); idx1++) {
	// tmpOfValues[1] = dom1.toVal(idx1);
	// cnt++;
	// if (evaluationManager.evaluate(tmpOfValues) != 1) {
	// tmpOfIndexes[1] = idx1;
	// removeTuple(tmpOfIndexes);
	// }
	// }
	// }
	// pb.stuff.nConvertionCcks += cnt;
	// mapOfExtensionStructures.put(key, extStructure);
	// } else {
	// extStructure = (ExtensionStructureHard) mapOfExtensionStructures.get(key);
	// extStructure.addDependentCtr(this);
	// conflictsStructure = extStructure.getFirstDependentCtr().getConflictsStructure();
	// if (conflictsStructure != null)
	// conflictsStructure.getExploitingConstraints().add(this);
	// ;
	// }
	// }

	public void logicalAndWithLessThanOrEqual(Variable x, Variable y) {
		throw new MissingImplementationException();

		// Kit.control(scp.length == 2);
		// this.id = id == null ? null : id + "_sble";
		// this.key += " " + "_sble"; //Kit.join(tree.canonicalForm(new ArrayList<>(), tree.vars()).toArray(new String[0]));
		// extStructure.removeDependentCtr(this);
		// if (conflictsStructure != null) {
		// conflictsStructure.getExploitingConstraints().remove(this);
		// conflictsStructure = new ConflictsStructure(conflictsStructure, this);
		// }
		// Map<String, ExtensionStructure> mapOfExtensionStructures = pb.resolution.mapOfExtensionStructures;
		// if (!mapOfExtensionStructures.containsKey(key)) {
		// extStructure = new Bits(this, (Bits) extStructure);
		// EvaluationManager evaluationManager = new EvaluationManager(tree); // Symbolic.replaceSymbols(pb.symbolic,
		// universalFragmentPredicateExpression));
		// int cnt = 0;
		// Domain dom0 = scp[0].dom, dom1 = scp[1].dom;
		// int[] tmpOfValues = tupleManager.localTuple, tmpOfIndexes = new int[2];
		// for (int idx0 = 0; idx0 < dom0.initSize(); idx0++) {
		// tmpOfValues[0] = dom0.toVal(idx0);
		// tmpOfIndexes[0] = idx0;
		// for (int idx1 = 0; idx1 < dom1.initSize(); idx1++) {
		// tmpOfValues[1] = dom1.toVal(idx1);
		// cnt++;
		// if (evaluationManager.evaluate(tmpOfValues) != 1) {
		// tmpOfIndexes[1] = idx1;
		// removeTuple(tmpOfIndexes);
		// }
		// }
		// }
		// pb.stuff.nConvertionCcks += cnt;
		// mapOfExtensionStructures.put(key, extStructure);
		// } else {
		// extStructure = (ExtensionStructureHard) mapOfExtensionStructures.get(key);
		// extStructure.addDependentCtr(this);
		// conflictsStructure = extStructure.getFirstDependentCtr().getConflictsStructure();
		// if (conflictsStructure != null)
		// conflictsStructure.getExploitingConstraints().add(this);
		// ;
		// }
		//
		//
		// //updateBitsFrom((XNodeParent<? extends IVarInteger>) pb.le(x, y)); // new String[] { "%" + positionOf(v2), "%" + positionOf(v1),
		// TypeExpr.LE.lcname
		// });
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

	@Override
	public Map<String, Object> mapXCSP() {
		Object tuples = scp[0] instanceof VariableInteger ? extStructure.originalTuples : pb.symbolic.mapOfTuples.get(this);
		return map(SCOPE, scp, LIST, compactOrdered(scp), ARITY, scp.length, TUPLES, tuples, POSITIVE, extStructure.originalPositive);
	}

}