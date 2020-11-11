/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.ge;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.lt;
import static org.xcsp.common.predicates.XNodeParent.ne;
import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.modeler.definitions.DefXCSP;
import org.xcsp.modeler.definitions.ICtr.ICtrSmart;

import constraints.Constraint;
import constraints.extension.CtrExtension.CtrExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.SmartTuple;
import constraints.extension.structures.TableSmart;
import problem.Problem;
import propagation.order1.StrongConsistency;
import utility.Kit;
import utility.sets.SetDenseReversible;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;

public final class CtrExtensionSmart extends CtrExtensionGlobal implements ICtrSmart {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static Constraint buildAllEqual(Problem pb, Variable[] list) {
		SmartTuple st = new SmartTuple(IntStream.range(1, list.length).mapToObj(i -> eq(list[0], list[i])).collect(Collectors.toList()));
		return new CtrExtensionSmart(pb, list, st);
	}

	public static Constraint buildNotAllEqual(Problem pb, Variable[] list) {
		SmartTuple[] sts = IntStream.range(1, list.length).mapToObj(i -> new SmartTuple(ne(list[0], list[i]))).toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, list, sts);
	}

	public static Constraint buildAtMost1(Problem pb, Variable[] list, Variable value) {
		Kit.control(!Kit.isPresent(value, list), () -> "Not handled for the moment");
		SmartTuple[] smartTuples = IntStream.range(0, list.length)
				.mapToObj(
						i -> new SmartTuple(IntStream.range(0, list.length).filter(j -> j != i).mapToObj(j -> ne(value, list[j])).collect(Collectors.toList())))
				.toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(list, value)), smartTuples);
	}

	public static Constraint buildElement(Problem pb, Variable[] list, Variable index, Variable value) {
		Kit.control(index.dom.firstValue() == 0 && !Kit.isPresent(value, list), () -> "Not handled for the moment");
		SmartTuple[] sts = IntStream.range(0, list.length).mapToObj(i -> new SmartTuple(eq(index, i), eq(list[i], value))).toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(list, index, value)), sts);
	}

	public static Constraint buildMinimum(Problem pb, Variable[] list, Variable min) {
		Kit.control(!Kit.isPresent(min, list), () -> "Not handled for the moment");
		SmartTuple[] smartTuples = IntStream.range(0, list.length)
				.mapToObj(i -> new SmartTuple(
						IntStream.range(0, list.length).mapToObj(j -> j != i ? le(list[i], list[j]) : eq(list[i], min)).collect(Collectors.toList())))
				.toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(list, min)), smartTuples);
	}

	public static Constraint buildMaximum(Problem pb, Variable[] list, Variable max) {
		Kit.control(!Kit.isPresent(max, list), () -> "Not handled for the moment");
		SmartTuple[] smartTuples = IntStream.range(0, list.length)
				.mapToObj(i -> new SmartTuple(
						IntStream.range(0, list.length).mapToObj(j -> j != i ? ge(list[i], list[j]) : eq(list[i], max)).collect(Collectors.toList())))
				.toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(list, max)), smartTuples);
	}

	public static Constraint buildLexicographicL(Problem pb, Variable[] t1, Variable[] t2, boolean strict) {
		Kit.control(t1.length == t2.length);
		SmartTuple[] smartTuples = IntStream.range(0, t1.length)
				.mapToObj(i -> new SmartTuple(IntStream.range(0, i + 1)
						.mapToObj(j -> j < i ? eq(t1[j], t2[j]) : i == t1.length - 1 ? le(t1[i], t2[i]) : lt(t1[i], t2[i])).collect(Collectors.toList())))
				.toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(t1, t2)), smartTuples);
	}

	public static Constraint buildNoOverlap(Problem pb, Variable x1, Variable x2, int w1, int w2) {
		SmartTuple st1 = new SmartTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		SmartTuple st2 = new SmartTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CtrExtensionSmart(pb, pb.vars(x1, x2), st1, st2);
	}

	public static Constraint buildNoOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, int w1, int h1, int w2, int h2) {
		SmartTuple st1 = new SmartTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		SmartTuple st2 = new SmartTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		SmartTuple st3 = new SmartTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		SmartTuple st4 = new SmartTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CtrExtensionSmart(pb, pb.vars(x1, y1, x2, y2), st1, st2, st3, st4);
	}

	public static Constraint buildNoOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, Variable h1, Variable w2,
			Variable h2) {
		Kit.control(w1.dom.size() == 2 && h1.dom.size() == 2 && w2.dom.size() == 2 && h2.dom.size() == 2);
		SmartTuple st1 = new SmartTuple(eq(w1, w1.dom.firstValue()), ge(x2, add(x1, w1.dom.firstValue())));
		SmartTuple st2 = new SmartTuple(eq(w1, w1.dom.lastValue()), ge(x2, add(x1, w1.dom.lastValue())));
		SmartTuple st3 = new SmartTuple(eq(w2, w2.dom.firstValue()), ge(x1, add(x2, w2.dom.firstValue())));
		SmartTuple st4 = new SmartTuple(eq(w2, w2.dom.lastValue()), ge(x1, add(x2, w2.dom.lastValue())));
		SmartTuple st5 = new SmartTuple(eq(h1, h1.dom.firstValue()), ge(y2, add(y1, h1.dom.firstValue())));
		SmartTuple st6 = new SmartTuple(eq(h1, h1.dom.lastValue()), ge(y2, add(y1, h1.dom.lastValue())));
		SmartTuple st7 = new SmartTuple(eq(h2, h2.dom.firstValue()), ge(y1, add(y2, h2.dom.firstValue())));
		SmartTuple st8 = new SmartTuple(eq(h2, h2.dom.lastValue()), ge(y1, add(y2, h2.dom.lastValue())));
		return new CtrExtensionSmart(pb, pb.vars(x1, y1, x2, y2, w1, h1, w2, h2), new SmartTuple[] { st1, st2, st3, st4, st5, st6, st7, st8 });
	}

	public static Constraint buildDistinctVectors(Problem pb, Variable[] t1, Variable[] t2) {
		Kit.control(t1.length == t2.length);
		Variable[] tt1 = IntStream.range(0, t1.length).anyMatch(i -> t1[i] == t2[i])
				? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t1[i]).toArray(Variable[]::new)
				: t1;
		Variable[] tt2 = IntStream.range(0, t1.length).anyMatch(i -> t1[i] == t2[i])
				? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t2[i]).toArray(Variable[]::new)
				: t2;
		Kit.control(tt1.length == tt2.length);
		SmartTuple[] smartTuples = IntStream.range(0, tt1.length).mapToObj(i -> new SmartTuple(ne(tt1[i], tt2[i]))).toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(pb, pb.distinctSorted(pb.vars(tt1, tt2)), smartTuples);
	}

	/**********************************************************************************************
	 * Restoration
	 *********************************************************************************************/

	private static final int UNINITIALIZED_VALUE = Integer.MAX_VALUE;

	protected int lastDepth;

	protected int[] lastSizes; // [vap] ; value = last domain sizes
	protected int[][] lastSizesStack; // 1D = level ; 2D = variable position

	@SuppressWarnings("unused")
	private boolean backtrack;

	// protected void buildRestorationStructures() {
	// Arrays.fill((lastSizesStack = new int[pb.variables.length + 1][scp.length])[0], UNINITIALIZED_VALUE);
	// }

	protected void initRestorationStructuresBeforeFiltering() {
		int depth = pb.solver.depth();
		assert depth >= lastDepth && lastDepth >= 0 : depth + " " + lastDepth;
		for (int i = lastDepth + 1; i <= depth; i++)
			System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, lastSizesStack[lastDepth].length);
		lastSizes = lastSizesStack[depth];
		lastDepth = depth;
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		set = new SetDenseReversible(smartTuples.length, pb.variables.length + 1);
		Arrays.fill((lastSizesStack = new int[pb.variables.length + 1][scp.length])[0], UNINITIALIZED_VALUE);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		// buildRestorationStructures();
		lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		backtrack = true;
	}

	// public void reinitLastSizes() {
	// Arrays.fill(lastSizesStack[0], UNINITIALIZED_VALUE);
	// Arrays.fill(lastSizes, UNINITIALIZED_VALUE);
	// }

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	public final SmartTuple[] smartTuples; // redundant field (reference to tuples in Table)

	protected SetDenseReversible set;

	public SetSparse[] unsupported;

	protected int sValSize;
	protected int[] sVal; // positions of the variables for which validity must be checked

	protected int sSupSize;
	protected int[] sSup; // positions of the variables for which GAC of values must be checked

	protected long lastCallNode;

	public CtrExtensionSmart(Problem pb, Variable[] scp, SmartTuple... smartTuples) {
		super(pb, scp);
		this.smartTuples = smartTuples;
		extStructure = buildExtensionStructure();
		unsupported = IntStream.range(0, scp.length).mapToObj(i -> new SetSparse(scp[i].dom.initSize(), true)).toArray(SetSparse[]::new);
		Stream.of(smartTuples).forEach(st -> st.attach(this));
		sVal = new int[scp.length];
		sSup = new int[scp.length];
		// Stream.of(smartTuples).forEach(st -> System.out.println(st));
	}

	@Override
	public ExtensionStructure buildExtensionStructure() {
		return new TableSmart(this, smartTuples);
	}

	protected void manageLastPastVariable() {
		if (lastCallNode != pb.solver.stats.nAssignments || pb.solver.propagation instanceof StrongConsistency) { // second condition due to Inverse4
			lastCallNode = pb.solver.stats.nAssignments;
			Variable lastPast = pb.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1)
				sVal[sValSize++] = x;
		}
	}

	protected void beforeFiltering() {
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVariable();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			Domain dom = scp[x].dom;
			if (dom.size() == lastSizes[x]) {
				// if (!backtrack && dom.getSize() == lastSizes[vap])
				unsupported[x].limit = lastSizes[x] - 1;
				// Kit.control(scp[vap].dom.isExactly(supportlesss[vap])); // TODO TO MODIFY AS AN ASSERT
				// *************************************************
			} else {
				unsupported[x].clear();
				for (int a = dom.first(); a != -1; a = dom.next(a))
					unsupported[x].add(a);
				backtrack = false;
			}
			int domSize = dom.size();
			if (lastSizes[x] != domSize) {
				sVal[sValSize++] = x;
				lastSizes[x] = domSize;
			}
			sSup[sSupSize++] = x;
		}
	}

	protected boolean updateDomains() {
		for (int i = 0; i < sSupSize; i++) {
			int x = sSup[i];
			assert !unsupported[x].isEmpty();
			if (scp[x].dom.remove(unsupported[x]) == false)
				return false;
			unsupported[x].moveElementsAt(lastSizes[x] - 1);
			lastSizes[x] = scp[x].dom.size();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		pb.stuff.updateStatsForSTR(set);
		int depth = pb.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			SmartTuple st = smartTuples[set.dense[i]];
			boolean valid = st.isValid(sVal, sValSize);
			if (valid) {
				sSupSize = st.collect(sSup, sSupSize);
			} else
				set.removeAtPosition(i, depth);
		}
		return updateDomains();
	}

	@Override
	public Map<String, Object> mapXCSP() {
		String[] rows = Stream.of(smartTuples)
				.map(st -> " (" + IntStream.of(st.prefixWithValues).mapToObj(v -> v == Constants.STAR ? "*" : v + "").collect(Collectors.joining(",")) + ") : "
						+ st.collectedTreeRestrictions.stream().map(t -> t.toString()).collect(Collectors.joining(" ")))
				.toArray(String[]::new);
		return map(SCOPE, scp, LIST, compactOrdered(scp), ROWS, rows);
	}

	@Override
	public DefXCSP defXCSP() {
		return ICtrSmart.super.defXCSP();
	}
}
