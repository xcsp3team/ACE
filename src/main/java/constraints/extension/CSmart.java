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

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.TableSmart;
import constraints.extension.structures.TableSmart.HybridTuple;
import problem.Problem;
import propagation.StrongConsistency;
import sets.SetDenseReversible;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class CSmart extends ExtensionSpecific {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static Constraint allEqual(Problem pb, Variable[] list) {
		HybridTuple ht = new HybridTuple(IntStream.range(1, list.length).mapToObj(i -> eq(list[0], list[i])));
		return new CSmart(pb, list, ht);
	}

	public static Constraint notAllEqual(Problem pb, Variable[] list) {
		Stream<HybridTuple> hts = IntStream.range(1, list.length).mapToObj(i -> new HybridTuple(ne(list[0], list[i])));
		return new CSmart(pb, list, hts);
	}

	public static Constraint atMost1(Problem pb, Variable[] list, Variable value) {
		Kit.control(!Kit.isPresent(value, list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).filter(j -> j != i).mapToObj(j -> ne(value, list[j]))));
		return new CSmart(pb, pb.distinctSorted(pb.vars(list, value)), hts);
	}

	public static Constraint element(Problem pb, Variable[] list, Variable index, Variable value) {
		Variable[] scp = pb.distinct(pb.vars(list, index, value));
		Kit.control(index.dom.firstValue() == 0 && scp.length == list.length + 2, () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length).mapToObj(i -> new HybridTuple(eq(index, i), eq(list[i], value)));
		return new CSmart(pb, scp, hts);
	}

	public static Constraint minimum(Problem pb, Variable[] list, Variable min) {
		Kit.control(!Kit.isPresent(min, list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).mapToObj(j -> j != i ? le(list[i], list[j]) : eq(list[i], min))));
		return new CSmart(pb, pb.distinctSorted(pb.vars(list, min)), hts);
	}

	public static Constraint maximum(Problem pb, Variable[] list, Variable max) {
		Kit.control(!Kit.isPresent(max, list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).mapToObj(j -> j != i ? ge(list[i], list[j]) : eq(list[i], max))));
		return new CSmart(pb, pb.distinctSorted(pb.vars(list, max)), hts);
	}

	public static Constraint lexicographicL(Problem pb, Variable[] t1, Variable[] t2, boolean strict) {
		Kit.control(t1.length == t2.length);
		Stream<HybridTuple> hts = IntStream.range(0, t1.length).mapToObj(i -> new HybridTuple(
				IntStream.range(0, i + 1).mapToObj(j -> j < i ? eq(t1[j], t2[j]) : i == t1.length - 1 ? le(t1[i], t2[i]) : lt(t1[i], t2[i]))));
		return new CSmart(pb, pb.distinctSorted(pb.vars(t1, t2)), hts);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable x2, int w1, int w2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CSmart(pb, pb.vars(x1, x2), ht1, ht2);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, int w1, int h1, int w2, int h2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CSmart(pb, pb.vars(x1, y1, x2, y2), ht1, ht2, ht3, ht4);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, Variable h1, Variable w2, Variable h2) {
		Kit.control(w1.dom.size() == 2 && h1.dom.size() == 2 && w2.dom.size() == 2 && h2.dom.size() == 2);
		HybridTuple ht1 = new HybridTuple(eq(w1, w1.dom.firstValue()), ge(x2, add(x1, w1.dom.firstValue())));
		HybridTuple ht2 = new HybridTuple(eq(w1, w1.dom.lastValue()), ge(x2, add(x1, w1.dom.lastValue())));
		HybridTuple ht3 = new HybridTuple(eq(w2, w2.dom.firstValue()), ge(x1, add(x2, w2.dom.firstValue())));
		HybridTuple ht4 = new HybridTuple(eq(w2, w2.dom.lastValue()), ge(x1, add(x2, w2.dom.lastValue())));
		HybridTuple ht5 = new HybridTuple(eq(h1, h1.dom.firstValue()), ge(y2, add(y1, h1.dom.firstValue())));
		HybridTuple ht6 = new HybridTuple(eq(h1, h1.dom.lastValue()), ge(y2, add(y1, h1.dom.lastValue())));
		HybridTuple ht7 = new HybridTuple(eq(h2, h2.dom.firstValue()), ge(y1, add(y2, h2.dom.firstValue())));
		HybridTuple ht8 = new HybridTuple(eq(h2, h2.dom.lastValue()), ge(y1, add(y2, h2.dom.lastValue())));
		return new CSmart(pb, pb.vars(x1, y1, x2, y2, w1, h1, w2, h2), ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8);
	}

	public static Constraint distinctVectors(Problem pb, Variable[] t1, Variable[] t2) {
		Kit.control(t1.length == t2.length);
		boolean match = IntStream.range(0, t1.length).anyMatch(i -> t1[i] == t2[i]);
		Variable[] tt1 = match ? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t1[i]).toArray(Variable[]::new) : t1;
		Variable[] tt2 = match ? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t2[i]).toArray(Variable[]::new) : t2;
		Kit.control(tt1.length == tt2.length);
		Stream<HybridTuple> hts = IntStream.range(0, tt1.length).mapToObj(i -> new HybridTuple(ne(tt1[i], tt2[i])));
		return new CSmart(pb, pb.distinctSorted(pb.vars(tt1, tt2)), hts);
	}

	/**********************************************************************************************
	 * Restoration
	 *********************************************************************************************/

	private static final int UNINITIALIZED = -2; // Integer.MAX_VALUE;

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.set = new SetDenseReversible(hybridTuples.length, problem.variables.length + 1);
		this.lastSizesStack = new int[problem.variables.length + 1][scp.length];
		Arrays.fill(lastSizesStack[0], UNINITIALIZED);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		backtrack = true;
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	public final HybridTuple[] hybridTuples; // redundant field (reference to tuples in Table)

	protected SetDenseReversible set;

	/**
	 * The sparse sets used during filtering: nac[x] is the sparse set for indexes (of values) of x, which have not been found a support yet (nac stands for not
	 * arc-consistent).
	 */
	public SetSparse[] nac;

	protected int sValSize;
	protected int[] sVal; // positions of the variables for which validity must be checked

	protected int sSupSize;
	protected int[] sSup; // positions of the variables for which GAC of values must be checked

	protected int[] lastSizes; // [vap] ; value = last domain sizes
	protected int[][] lastSizesStack; // 1D = level ; 2D = variable position

	protected int lastDepth;

	protected long lastSafeNumber;

	@SuppressWarnings("unused")
	private boolean backtrack;

	public CSmart(Problem pb, Variable[] scp, HybridTuple... smartTuples) {
		super(pb, scp);
		this.hybridTuples = smartTuples;
		this.extStructure = buildExtensionStructure();
		this.nac = IntStream.range(0, scp.length).mapToObj(i -> new SetSparse(scp[i].dom.initSize(), true)).toArray(SetSparse[]::new);
		Stream.of(smartTuples).forEach(st -> st.attach(this));
		this.sVal = new int[scp.length];
		this.sSup = new int[scp.length];
		// Stream.of(hybridTuples).forEach(t -> System.out.println(t));
	}

	public CSmart(Problem pb, Variable[] scp, Stream<HybridTuple> smartTuples) {
		this(pb, scp, smartTuples.toArray(HybridTuple[]::new));
	}

	@Override
	public ExtensionStructure buildExtensionStructure() {
		return new TableSmart(this, hybridTuples);
	}

	protected void initRestorationStructuresBeforeFiltering() {
		int depth = problem.solver.depth();
		assert 0 <= lastDepth && lastDepth <= depth : depth + " " + lastDepth + " " + this;
		for (int i = lastDepth + 1; i <= depth; i++)
			System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, lastSizesStack[lastDepth].length);
		lastSizes = lastSizesStack[depth];
		lastDepth = depth;
	}

	protected void manageLastPastVariable() {
		if (lastSafeNumber != problem.solver.stats.safeNumber() || problem.solver.propagation instanceof StrongConsistency) { // 2nd condition due to Inverse4
			lastSafeNumber = problem.solver.stats.safeNumber();
			Variable lastPast = problem.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				sVal[sValSize++] = x;
				lastSizes[x] = 1;
			}
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
				nac[x].limit = lastSizes[x] - 1;
				// Kit.control(scp[vap].dom.isExactly(supportlesss[vap])); // TODO TO MODIFY AS AN ASSERT
				// *************************************************
			} else {
				nac[x].clear();
				for (int a = dom.first(); a != -1; a = dom.next(a))
					nac[x].add(a);
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
			assert !nac[x].isEmpty();
			if (scp[x].dom.remove(nac[x]) == false)
				return false;
			nac[x].moveElementsAt(lastSizes[x] - 1);
			lastSizes[x] = scp[x].dom.size();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			HybridTuple hybridTuple = hybridTuples[set.dense[i]];
			if (hybridTuple.isValid(sVal, sValSize))
				sSupSize = hybridTuple.collect(sSup, sSupSize);
			else
				set.removeAtPosition(i, depth);
		}
		return updateDomains();
	}

}
