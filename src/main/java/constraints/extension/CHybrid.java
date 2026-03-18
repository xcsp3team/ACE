/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension;

import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.ge;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.lt;
import static org.xcsp.common.predicates.XNodeParent.ne;
import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.ConstraintExtension.ConstraintExtensionSpecific;
import constraints.extension.structures.TableHybrid;
import constraints.extension.structures.TableHybrid.HybridTuple;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import problem.Problem;
import sets.SetDenseReversible;
import sets.SetSparse;
import variables.Domain;
import variables.Variable;

/**
 * This is the code for CHybrid to deal with so-called hybrid/smart tables. The code follows a Simple Tabular Reduction (STR) general scheme. See "The Smart
 * Table Constraint", CPAIOR 2015: 271-287, by J.-B. Mairy, Y. Deville, and C. Lecoutre. <br />
 * IMPORTANT: the code is under revision, and is planned to be finalized within the end of year 2021.
 * 
 * 
 * TODO : Bug for java -ea ace BallSort2-agrressive-instance01.xml -valh=Asgs -trace
 * 
 * @author Christophe Lecoutre
 */
public final class CHybrid extends ConstraintExtensionSpecific implements ObserverOnBacktracksSystematic {

	/**********************************************************************************************
	 * Static methods
	 *********************************************************************************************/

	public static Constraint allEqual(Problem pb, Variable[] list) {
		HybridTuple ht = new HybridTuple(IntStream.range(1, list.length).mapToObj(i -> eq(list[0], list[i])));
		return new CHybrid(pb, list, ht);
	}

	public static Constraint notAllEqual(Problem pb, Variable[] list) {
		Stream<HybridTuple> hts = IntStream.range(1, list.length).mapToObj(i -> new HybridTuple(ne(list[0], list[i])));
		return new CHybrid(pb, list, hts);
	}

	public static Constraint atMost1(Problem pb, Variable[] list, Variable value) {
		control(!value.presentIn(list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).filter(j -> j != i).mapToObj(j -> ne(value, list[j]))));
		return new CHybrid(pb, pb.distinctSorted(pb.vars(list, value)), hts);
	}

	public static Constraint element(Problem pb, Variable[] list, Variable index, Variable value) {
		Variable newindex = Utilities.indexOf(index, list) != -1 ? pb.replaceByOtherVariable((Var) index) : index;
		Variable newvalue = Utilities.indexOf(value, list) != -1 ? pb.replaceByOtherVariable((Var) value) : value;
		Variable[] scp = pb.distinct(pb.vars(list, newindex, newvalue));
		control(newindex.dom.firstValue() == 0 && scp.length == list.length + 2, () -> "Not handled for the moment ");
		Stream<HybridTuple> hts = IntStream.range(0, list.length).mapToObj(i -> new HybridTuple(eq(newindex, i), eq(list[i], newvalue)));
		return new CHybrid(pb, scp, hts);
	}

	public static Constraint minimum(Problem pb, Variable[] list, Variable min) {
		control(!min.presentIn(list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).mapToObj(j -> j != i ? le(list[i], list[j]) : eq(list[i], min))));
		return new CHybrid(pb, pb.distinctSorted(pb.vars(list, min)), hts);
	}

	public static Constraint maximum(Problem pb, Variable[] list, Variable max) {
		control(!max.presentIn(list), () -> "Not handled for the moment");
		Stream<HybridTuple> hts = IntStream.range(0, list.length)
				.mapToObj(i -> new HybridTuple(IntStream.range(0, list.length).mapToObj(j -> j != i ? ge(list[i], list[j]) : eq(list[i], max))));
		return new CHybrid(pb, pb.distinctSorted(pb.vars(list, max)), hts);
	}

	public static Constraint lexicographicL(Problem pb, Variable[] t1, Variable[] t2, boolean strict) {
		control(t1.length == t2.length);
		Stream<HybridTuple> hts = IntStream.range(0, t1.length).mapToObj(i -> new HybridTuple(
				IntStream.range(0, i + 1).mapToObj(j -> j < i ? eq(t1[j], t2[j]) : i == t1.length - 1 ? le(t1[i], t2[i]) : lt(t1[i], t2[i]))));
		return new CHybrid(pb, pb.distinctSorted(pb.vars(t1, t2)), hts);
	}

	// 1D, widths being constants

	public static Constraint noOverlap(Problem pb, Variable x1, Variable x2, int w1, int w2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CHybrid(pb, pb.vars(x1, x2), ht1, ht2);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable x2, int w1, int w2, Variable aux) {
		control(aux.dom.initiallyRange(2));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CHybrid(pb, pb.vars(x1, x2, aux), ht1, ht2);
	}

	// 1D, widths being variables

	public static Constraint noOverlap(Problem pb, Variable x1, Variable x2, Variable w1, Variable w2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CHybrid(pb, pb.vars(x1, x2, w1, w2), ht1, ht2);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable x2, Variable w1, Variable w2, Variable aux) {
		control(aux.dom.initiallyRange(2));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		return new CHybrid(pb, pb.vars(x1, x2, w1, w2, aux), ht1, ht2);
	}

	// 2D, widths and lengths being constants

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, int w1, int h1, int w2, int h2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2), ht1, ht2, ht3, ht4);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, int w1, int h1, int w2, int h2, Variable aux) {
		control(aux.dom.initiallyRange(4));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(eq(aux, 2), ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(eq(aux, 3), ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, aux), ht1, ht2, ht3, ht4);
	}

	// 2D, widths being variables and lengths being constants

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, int h1, Variable w2, int h2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, w1, w2), ht1, ht2, ht3, ht4);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, int h1, Variable w2, int h2, Variable aux) {
		control(aux.dom.initiallyRange(4));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(eq(aux, 2), ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(eq(aux, 3), ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, w1, w2, aux), ht1, ht2, ht3, ht4);
	}

	// 2D, widths and lengths being variables

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, Variable h1, Variable w2, Variable h2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, w1, h1, w2, h2), ht1, ht2, ht3, ht4);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, Variable h1, Variable w2, Variable h2,
			Variable aux) {
		control(aux.dom.initiallyRange(4));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(eq(aux, 2), ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(eq(aux, 3), ge(y1, add(y2, h2))); // y1 >= y2 + h2
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, w1, h1, w2, h2, aux), ht1, ht2, ht3, ht4);
	}

	// 3D, widths and lengths being variables

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable z1, Variable x2, Variable y2, Variable z2, Variable w1, Variable h1,
			Variable d1, Variable w2, Variable h2, Variable d2) {
		HybridTuple ht1 = new HybridTuple(ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(ge(y1, add(y2, h2))); // y1 >= y2 + h2
		HybridTuple ht5 = new HybridTuple(ge(z2, add(z1, d1))); // z2 >= z1 + d1
		HybridTuple ht6 = new HybridTuple(ge(z1, add(z2, d2))); // z1 >= z2 + d2
		return new CHybrid(pb, pb.vars(x1, y1, z1, x2, y2, z2, w1, h1, d1, w2, h2, d2), ht1, ht2, ht3, ht4, ht5, ht6);
	}

	public static Constraint noOverlap(Problem pb, Variable x1, Variable y1, Variable z1, Variable x2, Variable y2, Variable z2, Variable w1, Variable h1,
			Variable d1, Variable w2, Variable h2, Variable d2, Variable aux) {
		control(aux.dom.initiallyRange(6));
		HybridTuple ht1 = new HybridTuple(eq(aux, 0), ge(x2, add(x1, w1))); // x2 >= x1 + w1
		HybridTuple ht2 = new HybridTuple(eq(aux, 1), ge(x1, add(x2, w2))); // x1 >= x2 + w2
		HybridTuple ht3 = new HybridTuple(eq(aux, 2), ge(y2, add(y1, h1))); // y2 >= y1 + h1
		HybridTuple ht4 = new HybridTuple(eq(aux, 3), ge(y1, add(y2, h2))); // y1 >= y2 + h2
		HybridTuple ht5 = new HybridTuple(eq(aux, 4), ge(z2, add(z1, d1))); // z2 >= z1 + d1
		HybridTuple ht6 = new HybridTuple(eq(aux, 5), ge(z1, add(z2, d2))); // z1 >= z2 + d2
		return new CHybrid(pb, pb.vars(x1, y1, z1, x2, y2, z2, w1, h1, d1, w2, h2, d2, aux), ht1, ht2, ht3, ht4, ht5, ht6);
	}

	// special case (TODO : to be checked if this remains relevant/interesting)

	public static Constraint noOverlapBin(Problem pb, Variable x1, Variable y1, Variable x2, Variable y2, Variable w1, Variable h1, Variable w2, Variable h2) {
		control(w1.dom.size() == 2 && h1.dom.size() == 2 && w2.dom.size() == 2 && h2.dom.size() == 2);
		HybridTuple ht1 = new HybridTuple(eq(w1, w1.dom.firstValue()), ge(x2, add(x1, w1.dom.firstValue())));
		HybridTuple ht2 = new HybridTuple(eq(w1, w1.dom.lastValue()), ge(x2, add(x1, w1.dom.lastValue())));
		HybridTuple ht3 = new HybridTuple(eq(w2, w2.dom.firstValue()), ge(x1, add(x2, w2.dom.firstValue())));
		HybridTuple ht4 = new HybridTuple(eq(w2, w2.dom.lastValue()), ge(x1, add(x2, w2.dom.lastValue())));
		HybridTuple ht5 = new HybridTuple(eq(h1, h1.dom.firstValue()), ge(y2, add(y1, h1.dom.firstValue())));
		HybridTuple ht6 = new HybridTuple(eq(h1, h1.dom.lastValue()), ge(y2, add(y1, h1.dom.lastValue())));
		HybridTuple ht7 = new HybridTuple(eq(h2, h2.dom.firstValue()), ge(y1, add(y2, h2.dom.firstValue())));
		HybridTuple ht8 = new HybridTuple(eq(h2, h2.dom.lastValue()), ge(y1, add(y2, h2.dom.lastValue())));
		return new CHybrid(pb, pb.vars(x1, y1, x2, y2, w1, h1, w2, h2), ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8);
	}

	public static Constraint distinctVectors(Problem pb, Variable[] t1, Variable[] t2) {
		control(t1.length == t2.length);
		boolean match = IntStream.range(0, t1.length).anyMatch(i -> t1[i] == t2[i]);
		Variable[] tt1 = match ? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t1[i]).toArray(Variable[]::new) : t1;
		Variable[] tt2 = match ? IntStream.range(0, t1.length).filter(i -> t1[i] != t2[i]).mapToObj(i -> t2[i]).toArray(Variable[]::new) : t2;
		control(tt1.length == tt2.length);
		Stream<HybridTuple> hts = IntStream.range(0, tt1.length).mapToObj(i -> new HybridTuple(ne(tt1[i], tt2[i])));
		return new CHybrid(pb, pb.distinctSorted(pb.vars(tt1, tt2)), hts);
	}

	/**********************************************************************************************
	 * Restoration
	 *********************************************************************************************/

	private static final int UNINITIALIZED = -2; // Integer.MAX_VALUE;

	@Override
	public void afterProblemConstruction(int n) {
		super.afterProblemConstruction(n);
		this.set = new SetDenseReversible(hybridTuples.length, n + 1);

		if (n < problem.head.control.extension.chybridStackingLimit) { // hard coding
			this.lastSizesStack = new int[n + 1][scp.length];
			Arrays.fill(lastSizesStack[0], UNINITIALIZED);
		} else
			this.lastSizesStack = null;
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		// backtrack = true;
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * The hybrid tuples of the table (redundant field)
	 */
	public final HybridTuple[] hybridTuples;

	/**
	 * The reversible dense set storing the indexes (of hybrid tuples) of the current table
	 */
	protected SetDenseReversible set;

	/**
	 * The sparse sets used during filtering: nac[x] is the sparse set for indexes (of values) of x, which have not been found a support yet (nac stands for not
	 * arc-consistent).
	 */
	public SetSparse[] nac;

	/**
	 * The (dense) set of positions of variables for which validity must be checked. Relevant positions are at indexes from 0 to sValSize (excluded).
	 */
	protected int[] sVal;

	/**
	 * The number of variables for which support searching must be done (i.e., variables with some values that still must be checked to be AC)
	 */
	protected int sValSize;

	/**
	 * The (dense) set of positions of variables for which support searching must be done. Relevant positions are at indexes from 0 to sSupSize (excluded).
	 */
	protected int[] sSup;

	/**
	 * The number of variables for which support searching must be done (i.e., variables with some values that still must be checked to be AC)
	 */
	protected int sSupSize;

	/**
	 * lastSizes[x] is the domain size of x at the last call
	 */
	protected int[] lastSizes;

	/**
	 * lastSizesStack[i][x] is the domain size of x at the last call at level (depth) i
	 */
	protected int[][] lastSizesStack;

	/**
	 * The depth at the last call
	 */
	protected int lastDepth;

	/**
	 * A number used to determine whether the last past variable should be considered for validity testing (and for possibly other roles in subclasses)
	 */
	protected long lastSafeNumber;

	// @SuppressWarnings("unused")
	// private boolean backtrack;

	/**
	 * Builds a hybrid table constraint
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param hybridTuples
	 *            the hybrid tuples of the constraint
	 */
	public CHybrid(Problem pb, Variable[] scp, HybridTuple... hybridTuples) {
		super(pb, scp);
		this.hybridTuples = hybridTuples;
		this.extStructure = new TableHybrid(this, hybridTuples);
		this.nac = IntStream.range(0, scp.length).mapToObj(i -> new SetSparse(scp[i].dom.initSize(), true)).toArray(SetSparse[]::new);
		for (HybridTuple hybridTuple : hybridTuples)
			hybridTuple.attach(this);
		this.sVal = new int[scp.length];
		this.sSup = new int[scp.length];
		// System.out.println(this + " " + Kit.join(hybridTuples));
	}

	/**
	 * Builds a hybrid table constraint
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 * @param hybridTuples
	 *            the hybrid tuples of the constraint
	 */
	public CHybrid(Problem pb, Variable[] scp, Stream<HybridTuple> hybridTuples) {
		this(pb, scp, hybridTuples.toArray(HybridTuple[]::new));
	}

	/**
	 * Makes, before filtering, some initialization with respect to the structures used for restoration
	 */
	protected void initRestorationStructuresBeforeFiltering() {
		if (lastSizesStack != null) {
			int depth = problem.solver.depth();
			assert 0 <= lastDepth && lastDepth <= depth : depth + " " + lastDepth + " " + this;
			for (int i = lastDepth + 1; i <= depth; i++)
				System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, lastSizesStack[lastDepth].length);
			lastSizes = lastSizesStack[depth];
			lastDepth = depth;
		}
	}

	/**
	 * Makes, before filtering, some initialization with respect to the last variable explicitly assigned by the solver
	 */
	protected void manageLastPastVariable() {
		if (lastSafeNumber != problem.solver.stats.safeNumber()) { // || problem.solver.propagation instanceof StrongConsistency) { // 2nd condition due to
																	// Inverse4
			lastSafeNumber = problem.solver.stats.safeNumber();
			Variable lastPast = problem.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				sVal[sValSize++] = x;
				if (lastSizesStack != null)
					lastSizes[x] = 1;
			}
		}
	}

	/**
	 * Performs some initializations before starting the filtering process.
	 */
	protected void beforeFiltering() {
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVariable();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			Domain dom = scp[x].dom;
			if (lastSizesStack != null) {
				if (dom.size() == lastSizes[x]) {
					// if (!backtrack && dom.size() == lastSizes[x])
					nac[x].limit = lastSizes[x] - 1;
					// control(scp[x].dom.isExactly(nac[x])); // TODO TO MODIFY AS AN ASSERT
					// *************************************************
				} else {
					nac[x].clear();
					for (int a = dom.first(); a != -1; a = dom.next(a))
						nac[x].add(a);
					// backtrack = false;
				}
				int domSize = dom.size();
				if (lastSizes[x] != domSize) {
					sVal[sValSize++] = x;
					lastSizes[x] = domSize;
				}
			} else {
				nac[x].clear();
				for (int a = dom.first(); a != -1; a = dom.next(a))
					nac[x].add(a);
				sVal[sValSize++] = x;
			}
			sSup[sSupSize++] = x;
		}
	}

	/**
	 * Updates the domains of the variables in the scope of the constraint at the end of the filtering process
	 * 
	 * @return false if an inconsistency (empty domain) is detected
	 */
	protected boolean updateDomains() {
		for (int i = 0; i < sSupSize; i++) {
			int x = sSup[i];
			assert !nac[x].isEmpty();
			if (scp[x].dom.remove(nac[x]) == false)
				return false;
			if (lastSizesStack != null) {
				nac[x].moveElementsAt(lastSizes[x] - 1);
				lastSizes[x] = scp[x].dom.size();
			}
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			HybridTuple hybridTuple = hybridTuples[set.dense[i]];
			if (!options.discardHybridEntailment && hybridTuple.isEntailed())
				return entail();
			if (hybridTuple.isValid(sVal, sValSize)) {
				sSupSize = hybridTuple.collect(sSup, sSupSize);
			} else
				set.removeAtPosition(i, depth);
		}
		return updateDomains();
	}

}
