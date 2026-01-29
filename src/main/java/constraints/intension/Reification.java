/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import static propagation.AC.enforceEQ;
import static propagation.AC.enforceGE;
import static propagation.AC.enforceGT;
import static propagation.AC.enforceLE;
import static propagation.AC.enforceLT;
import static propagation.AC.enforceNE;
import static utility.Kit.control;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeLogicalOperator;

import constraints.ConstraintSpecific;
import constraints.intension.Reification.ReifLogic.ReifLogic2.LogEqAnd2;
import constraints.intension.Reification.ReifLogic.ReifLogic2.LogEqOr2;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqAnd;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqIff;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqOr;
import constraints.intension.Reification.ReifLogic.ReifLogicn.LogEqXor;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import variables.Domain;
import variables.Variable;

public final class Reification {

	/**********************************************************************************************
	 * Binary Reification : Classes for x = (y <op> k) or w = (y <setop> S)
	 *********************************************************************************************/

	/**
	 * The root class for simple reification forms: a variable is defined as the result of a logical comparison involving another variable
	 */
	public static abstract class Reif2 extends Primitive2 implements TagNotSymmetric {

		public Reif2(Problem pb, Variable x, Variable y, int k) { // k not relevant for some subclasses
			super(pb, x, y, k);
			if (!dx.is01()) {
				control(dx.initSize() >= 2 && dx.toVal(0) == 0 && dx.toVal(1) == 1 && (dx.contains(0) && dx.contains(1)));
				dx.removeAtConstructionTime(v -> v > 1);
			}
			// control(dx.is01(), "The first variable should be of type 01 " + x);
		}

		public static abstract class Reif2Rel extends Reif2 {

			public static Reif2Rel buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Reif2LE(pb, x, y, k - 1);
				case LE:
					return new Reif2LE(pb, x, y, k);
				case GE:
					return new Reif2GE(pb, x, y, k);
				case GT:
					return new Reif2GE(pb, x, y, k + 1);
				case EQ:
					return new Reif2EQ(pb, x, y, k);
				default: // NE
					return new Reif2NE(pb, x, y, k);
				}
			}

			public Reif2Rel(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				// defineKey(k); // TODO pb because already called (something to change in the hierarchy)
			}

			public static final class Reif2LE extends Reif2Rel {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return (t[0] == 1) == (t[1] <= k);
				}

				public Reif2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0)
						return (dy.firstValue() > k || dy.removeValuesLE(k)) && entail(); // x = 0 => y > k
					if (dx.first() == 1)
						return (dy.lastValue() <= k || dy.removeValuesGT(k)) && entail(); // x = 1 => y <= k
					if (dy.lastValue() <= k)
						return dx.removeIfPresent(0) && entail(); // y <= k => x != 0
					if (dy.firstValue() > k)
						return dx.removeIfPresent(1) && entail(); // y > k => x != 1
					return true;
				}
			}

			public static final class Reif2GE extends Reif2Rel {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return (t[0] == 1) == (t[1] >= k);
				}

				public Reif2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0)
						return (dy.lastValue() < k || dy.removeValuesGE(k)) && entail(); // x = 0 => y < k
					if (dx.first() == 1)
						return (dy.firstValue() >= k || dy.removeValuesLT(k)) && entail(); // x = 1 => y >= k
					if (dy.firstValue() >= k)
						return dx.removeIfPresent(0) && entail(); // y >= k => x != 0
					if (dy.lastValue() < k)
						return dx.removeIfPresent(1) && entail(); // y < k => x != 1
					return true;
				}
			}

			public static final class Reif2EQ extends Reif2Rel {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return (t[0] == 1) == (t[1] == k);
				}

				public Reif2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0)
						return dy.removeValueIfPresent(k) && entail(); // x = 0 => y != k
					if (dx.first() == 1)
						return dy.reduceToValue(k) && entail(); // x = 1 => y = k
					if (!dy.containsValue(k))
						return dx.removeIfPresent(1) && entail(); // y != k => x != 1
					if (dy.size() == 1)
						return dx.removeIfPresent(0) && entail(); // y = k => x != 0
					return true;
				}
			}

			public static final class Reif2NE extends Reif2Rel {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return (t[0] == 1) == (t[1] != k);
				}

				public Reif2NE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0)
						return dy.reduceToValue(k) && entail(); // x = 0 => y = k
					if (dx.first() == 1)
						return dy.removeValueIfPresent(k) && entail(); // x = 1 => x != k
					if (!dy.containsValue(k))
						return dx.removeIfPresent(0) && entail(); // y != k => x != 0
					if (dy.size() == 1)
						return dx.removeIfPresent(1) && entail(); // y = k => x != 1
					return true;
				}
			}
		}

		public static abstract class Reif2Set extends Reif2 {

			public static Reif2Set buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorSet op, int[] values) {
				switch (op) {
				case IN:
					return new Reif2In(pb, x, y, values);
				default: // NOTIN
					throw new AssertionError("unimplemented case");
				}
			}

			int[] values;

			public Reif2Set(Problem pb, Variable x, Variable y, int[] values) {
				super(pb, x, y, -1); // -1 is a dummy value
				this.values = IntStream.of(values).sorted().toArray();
				// defineKey(values); // TODO pb because already called (something to change in the hierachy)
			}

			public static final class Reif2In extends Reif2Set {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					for (int v : values)
						if (v == t[1])
							return t[0] == 1;
					return t[0] == 0;
				}

				private int sentinelIn = -1, sentinelOut = -1; // storing indexes of values

				private boolean checkSentinelIn() {
					if (sentinelIn != -1 && dy.contains(sentinelIn))
						return true;
					for (int v : values)
						if (dy.containsValue(v)) {
							sentinelIn = dy.toIdx(v);
							return true;
						}
					return false;
				}

				private boolean checkSentinelOut() {
					if (dy.size() > values.length)
						return true;
					if (sentinelOut != -1 && dy.contains(sentinelOut))
						return true;
					int j = 0;
					for (int a = dy.first(); a != -1; a = dy.next(a)) {
						int v = dy.toVal(a);
						while (j < values.length && values[j] < v)
							j++;
						if (j == values.length || values[j] != v) {
							sentinelOut = a;
							return true;
						} else
							j++;
					}
					return false;
				}

				public Reif2In(Problem pb, Variable x, Variable y, int[] values) {
					super(pb, x, y, values);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0)
						return dy.removeValuesIn(values) && entail(); // x = 0 => y not in S
					if (dx.first() == 1)
						return dy.removeValuesNotIn(values) && entail(); // x = 1 => y in S

					if (!checkSentinelIn())
						return dx.remove(1) && entail();
					if (!checkSentinelOut())
						return dx.remove(0) && entail();
					return true;
				}
			}
		}
	}

	/**********************************************************************************************
	 * Ternary Reification : Classes for x = (y <op> z)
	 *********************************************************************************************/

	public static abstract class Reif3 extends Primitive3 {

		public static Reif3 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case LT:
				return new Reif3LT(pb, x, y, z);
			case LE:
				return new Reif3LE(pb, x, y, z);
			case GE:
				return new Reif3GE(pb, x, y, z);
			case GT:
				return new Reif3GT(pb, x, y, z);
			case EQ:
				return new Reif3EQ(pb, x, y, z);
			default: // NE
				return new Reif3NE(pb, x, y, z);
			}
		}

		public Reif3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
			control(dx.is01(), "The first variable should be of type 01");
		}

		public static final class Reif3LT extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] < t[2]);
			}

			public Reif3LT(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return enforceGE(dy, dz); // x = 0 => y >= z
				if (dx.first() == 1)
					return enforceLT(dy, dz); // x = 1 => y < z
				if (dy.lastValue() < dz.firstValue())
					return dx.removeIfPresent(0); // y < z => x != 0
				if (dy.firstValue() >= dz.lastValue())
					return dx.removeIfPresent(1); // y >= z => x != 1
				return true;
			}
		}

		public static final class Reif3LE extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] <= t[2]);
			}

			public Reif3LE(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return enforceGT(dy, dz); // x = 0 => y > z
				if (dx.first() == 1)
					return enforceLE(dy, dz); // x = 1 => y <= z
				if (dy.lastValue() <= dz.firstValue())
					return dx.removeIfPresent(0); // y <= z => x != 0
				if (dy.firstValue() > dz.lastValue())
					return dx.removeIfPresent(1); // y > z => x != 1
				return true;
			}
		}

		public static final class Reif3GE extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] >= t[2]);
			}

			public Reif3GE(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return enforceLT(dy, dz); // x = 0 => y < z
				if (dx.first() == 1)
					return enforceGE(dy, dz); // x = 1 => y >= z
				if (dy.firstValue() >= dz.lastValue())
					return dx.removeIfPresent(0); // y >= z => x != 0
				if (dy.lastValue() < dz.firstValue())
					return dx.removeIfPresent(1); // y < z => x != 1
				return true;
			}
		}

		public static final class Reif3GT extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] > t[2]);
			}

			public Reif3GT(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return enforceLE(dy, dz); // x = 0 => y <= z
				if (dx.first() == 1)
					return enforceGT(dy, dz); // x = 1 => y > z
				if (dy.firstValue() > dz.lastValue())
					return dx.removeIfPresent(0); // y > z => x != 0
				if (dy.lastValue() <= dz.firstValue())
					return dx.removeIfPresent(1); // y <= z => x != 1
				return true;
			}
		}

		public static final class Reif3EQ extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] == t[2]);
			}

			private int residue; // for a common value in the domains of y and z, supporting (x,1)

			public Reif3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.removeIfPresent(dy.firstValue() == dz.firstValue() ? 0 : 1); // remember that indexes and values match for x
				if (dx.last() == 0)
					return (dy.size() > 1 && dz.size() > 1) || (enforceNE(dy, dz) && entail()); // x = 0 => y != z
				if (dx.first() == 1)
					return enforceEQ(dy, dz); // x = 1 => y = z
				assert dx.size() == 2;
				// we know that (x,0) is supported because the domain of y and/or the domain of z is not singleton
				if (dy.containsValue(residue) && dz.containsValue(residue))
					return true;
				// we look for a support for (x,1), and record it as a residue
				int v = dy.commonValueWith(dz);
				if (v != Integer.MAX_VALUE)
					residue = v;
				else
					return dx.remove(1) && entail(); // since inconsistency not possible and dy and dz are disjoint
				return true;
			}
		}

		public static final class Reif3NE extends Reif3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return (t[0] == 1) == (t[1] != t[2]);
			}

			int residue; // for a common value in the domains of y and z, supporting (x,0)

			public Reif3NE(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.removeIfPresent(dy.firstValue() != dz.firstValue() ? 0 : 1); // remember that indexes and values match for x
				if (dx.last() == 0)
					return enforceEQ(dy, dz); // x = 0 => y = z
				if (dx.first() == 1)
					return (dy.size() > 1 && dz.size() > 1) || (enforceNE(dy, dz) && entail()); // x = 1 => y != z
				assert dx.size() == 2;
				// we know that (x,1) is supported because the domain of y and/or the domain of z is not singleton
				if (dy.containsValue(residue) && dz.containsValue(residue))
					return true;
				// we look for a support for (x,0), and record it as a residue
				int v = dy.commonValueWith(dz);
				if (v != Integer.MAX_VALUE)
					residue = v;
				else {
					return dx.remove(0) && entail(); // since inconsistency not possible and dy and dz are disjoint
				}
				return true;
			}
		}

	}

	public static final class DisjonctiveReified extends Primitive3 {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return ((t[2] == 0) && (t[0] + w1 <= t[1])) || ((t[2] == 1) && (t[1] + w2 <= t[0]));
		}

		private final int w1, w2;

		public DisjonctiveReified(Problem pb, Variable x, int w1, Variable y, int w2, Variable z) {
			super(pb, x, y, z);
			control(scp.length == 3 && z.dom.is01());
			this.w1 = w1;
			this.w2 = w2;
			defineKey(w1, w2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (problem.solver.justLastRefutedVariable())
				if (dummy.dom.lastRemovedInsideBounds())
					return true;

			if (dx.lastValue() + w1 <= dy.firstValue()) // x + wx <= y => z = 0
				return dz.removeIfPresent(1) && entail();
			if (dy.lastValue() + w2 <= dx.firstValue()) // y + wy <= x => z = 1
				return dz.removeIfPresent(0) && entail();

			if (dz.last() == 0) {// z = 0 => x + wx <= y
				if (enforceLE(dx, dy, -w1) == false)
					return false;
				if (dx.lastValue() + w1 <= dy.firstValue())
					return entail();
				return true;
			}
			if (dz.first() == 1) {// z = 1 => y + wy <= x
				if (enforceLE(dy, dx, -w2) == false)
					return false;
				if (dy.lastValue() + w2 <= dx.firstValue())
					return entail();
				return true;
			}
			return dx.removeValuesInRange(dy.lastValue() - w1 + 1, dy.firstValue() + w2)
					&& dy.removeValuesInRange(dx.lastValue() - w2 + 1, dx.firstValue() + w1);
		}
	}

	public static final class Disjonctive2Reified2Cst extends ConstraintSpecific implements TagNotAC, TagCallCompleteFiltering, TagNotSymmetric {
		// TODO TagNotAC ???

		final int w1, w2, h1, h2;

		final Domain dx1, dx2, dy1, dy2, dz;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return ((t[4] == 0) && (t[0] + w1 <= t[1])) || ((t[4] == 1) && (t[1] + w2 <= t[0])) || ((t[4] == 2) && (t[2] + h1 <= t[3]))
					|| ((t[4] == 3) && (t[3] + h2 <= t[2])); // (z=0 and x1+w1 <= x2) or (z=1 and x2+w2 <= x1) or (z=3 and y1+h1 <= y2) or (z=4 and y2+h2 <= y1)
		}

		public Disjonctive2Reified2Cst(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2, Variable z) {
			super(pb, new Variable[] { x1, x2, y1, y2, z });
			control(scp.length == 5 && z.dom.initiallyRange(4));
			this.w1 = w1;
			this.w2 = w2;
			this.h1 = h1;
			this.h2 = h2;
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			this.dz = z.dom;
			defineKey(w1, w2, h1, h2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (problem.solver.justLastRefutedVariable())
				if (dummy.dom.lastRemovedInsideBounds())
					return true;

			// Variable x = problem.solver.justLastRefutedVariable();
			// if (x != null) {
			// int a = problem.solver.decisions.idxOfLastDecision();
			// if (x.dom.first() < a && a < x.dom.last())
			// return true;
			// }

			int minx1 = dx1.firstValue() + w1, minx2 = dx2.firstValue() + w2;
			int miny1 = dy1.firstValue() + h1, miny2 = dy2.firstValue() + h2;
			boolean bx1 = minx1 <= dx2.lastValue(), bx2 = minx2 <= dx1.lastValue();
			boolean by1 = miny1 <= dy2.lastValue(), by2 = miny2 <= dy1.lastValue();

			if (!bx2 || (dx1.lastValue() + w1 <= dx2.firstValue())) // !bx2 or x1 + w1 <= x2 => z != 1
				if (dz.removeIfPresent(1) == false)
					return false;
			if (!bx1 || (dx2.lastValue() + w2 <= dx1.firstValue())) // !bx1 or x2 + w2 <= x1 => z != 0
				if (dz.removeIfPresent(0) == false)
					return false;
			if (!by2 || (dy1.lastValue() + h1 <= dy2.firstValue())) // !by2 or y1 + h1 <= y2 => z != 3
				if (dz.removeIfPresent(3) == false)
					return false;
			if (!by1 || (dy2.lastValue() + h2 <= dy1.firstValue())) // !by1 or y2 + h2 <= y1 => z != 2
				if (dz.removeIfPresent(2) == false)
					return false;
			if (dz.size() == 1) {
				if (dz.single() == 0) // z = 0 => x1 + w1 <= x2
					return enforceLE(dx1, dx2, -w1);
				if (dz.single() == 1) // z = 1 => x2 + w2 <= x1
					return enforceLE(dx2, dx1, -w2);
				if (dz.single() == 2) // z = 2 => y1 + h1 <= y2
					return enforceLE(dy1, dy2, -h1);
				if (dz.single() == 3) // z = 3 => y2 + h2 <= y1
					return enforceLE(dy2, dy1, -h2);
			}

			boolean bx = bx1 || bx2, by = by1 || by2;
			if (bx && by)
				return true;
			if (!bx && !by)
				return false;
			if (bx)
				return dx1.removeValuesInRange(dx2.lastValue() - w1 + 1, minx2) && dx2.removeValuesInRange(dx1.lastValue() - w2 + 1, minx1);
			return dy1.removeValuesInRange(dy2.lastValue() - h1 + 1, miny2) && dy2.removeValuesInRange(dy1.lastValue() - h2 + 1, miny1);
		}
	}

	public static final class Disjonctive2ReifiedVar extends ConstraintSpecific implements TagNotAC, TagCallCompleteFiltering, TagNotSymmetric {
		// TODO TagNotAC ???

		final Domain dx1, dx2, dy1, dy2, dw1, dw2, dh1, dh2, dz;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return ((t[8] == 0) && (t[0] + t[4] <= t[1])) || ((t[8] == 1) && (t[1] + t[5] <= t[0])) || ((t[8] == 2) && (t[2] + t[6] <= t[3]))
					|| ((t[8] == 3) && (t[3] + t[7] <= t[2])); // (z=0 and x1+w1 <= x2) or (z=1 and x2+w2 <= x1) or (z=2 and y1+h1 <= y2) or (z=3 and y2+h2<=y1)
		}

		public Disjonctive2ReifiedVar(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, Variable w1, Variable w2, Variable h1, Variable h2,
				Variable z) {
			super(pb, new Variable[] { x1, x2, y1, y2, w1, w2, h1, h2, z });
			control(scp.length == 9 && z.dom.initiallyRange(4));
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			this.dw1 = w1.dom;
			this.dw2 = w2.dom;
			this.dh1 = h1.dom;
			this.dh2 = h2.dom;
			this.dz = z.dom;
		}

		private int minx1, minx2, miny1, miny2;
		private boolean bx1, bx2, by1, by2;

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dz.size() > 1) {
				minx2 = dx2.firstValue() + dw2.firstValue();
				bx2 = minx2 <= dx1.lastValue();
				if (!bx2 || (dx1.lastValue() + dw1.lastValue() <= dx2.firstValue())) // !bx2 or x1 + w1 <= x2 => z != 1
					if (dz.removeIfPresent(1) == false)
						return false;

				minx1 = dx1.firstValue() + dw1.firstValue();
				bx1 = minx1 <= dx2.lastValue();
				if (!bx1 || (dx2.lastValue() + dw2.lastValue() <= dx1.firstValue())) // !bx1 or x2 + w2 <= x1 => z != 0
					if (dz.removeIfPresent(0) == false)
						return false;

				miny2 = dy2.firstValue() + dh2.firstValue();
				by2 = miny2 <= dy1.lastValue();
				if (!by2 || (dy1.lastValue() + dh1.lastValue() <= dy2.firstValue())) // !by2 or y1 + h1 <= y2 => z != 3
					if (dz.removeIfPresent(3) == false)
						return false;

				miny1 = dy1.firstValue() + dh1.firstValue();
				by1 = miny1 <= dy2.lastValue();
				if (!by1 || (dy2.lastValue() + dh2.lastValue() <= dy1.firstValue())) // !by1 or y2 + h2 <= y1 => z != 2
					if (dz.removeIfPresent(2) == false)
						return false;
			}
			if (dz.size() == 1) {
				if (dz.single() == 0) {// z = 0 => x1 + w1 <= x2
					if (enforceLE(dx1, dw1, dx2) == false)
						return false;
					// return true;
					return dx1.lastValue() + dw1.lastValue() <= dx2.firstValue() ? entail() : true;
				}
				if (dz.single() == 1) {// z = 1 => x2 + w2 <= x1
					if (enforceLE(dx2, dw2, dx1) == false)
						return false;
					// return true;
					return dx2.lastValue() + dw2.lastValue() <= dx1.firstValue() ? entail() : true;
				}
				if (dz.single() == 2) {// z = 2 => y1 + h1 <= y2
					if (enforceLE(dy1, dh1, dy2) == false)
						return false;
					// return true;
					return dy1.lastValue() + dh1.lastValue() <= dy2.firstValue() ? entail() : true;
				}
				if (dz.single() == 3) {// z = 3 => y2 + h2 <= y1
					if (enforceLE(dy2, dh2, dy1) == false)
						return false;
					// return true;
					return dy2.lastValue() + dh2.lastValue() <= dy1.firstValue() ? entail() : true;
				}
			}

			boolean bx = bx1 || bx2, by = by1 || by2;
			if (bx && by)
				return true;
			if (!bx && !by)
				return false;
			control(dz.size() == 2); // because otherwise z would have been reduced earlier
			if (bx) {
				control(bx1 && bx2);
				if (dx1.removeValuesInRange(dx2.lastValue() - dw1.firstValue() + 1, minx2) == false)
					return false;
				if (dx2.removeValuesInRange(dx1.lastValue() - dw2.firstValue() + 1, minx1) == false)
					return false;
				// if (!bx1)
				// if (dw2.removeValuesGT(dx1.lastValue() - dx2.firstValue()) == false)
				// return false;
				// if (!bx2)
				// if (dw1.removeValuesGT(dx2.lastValue() - dx1.firstValue()) == false)
				// return false;
				return true;
			} else {
				control(by1 && by2);
				if (dy1.removeValuesInRange(dy2.lastValue() - dh1.firstValue() + 1, miny2) == false)
					return false;
				if (dy2.removeValuesInRange(dy1.lastValue() - dh2.firstValue() + 1, miny1) == false)
					return false;
				// if (!by1)
				// if (dh2.removeValuesGT(dy1.lastValue() - dy2.firstValue()) == false)
				// return false;
				// if (!by2)
				// if (dh1.removeValuesGT(dy2.lastValue() - dy1.firstValue()) == false)
				// return false;
				return true;
				// return dy1.removeValuesInRange(dy2.lastValue() - h1 + 1, miny2) && dy2.removeValuesInRange(dy1.lastValue() - h2 + 1, miny1);
			}
		}
	}

	/**********************************************************************************************
	 * Logical Reification : Classes for x = (y and z), x = (y or z) and their extensions to more than two variables in the right term
	 *********************************************************************************************/

	public static abstract class ReifLogic extends Primitive implements TagAC, TagCallCompleteFiltering, TagNotSymmetric {

		public static ReifLogic buildFrom(Problem pb, Variable x, TypeLogicalOperator op, Variable[] list) {
			switch (op) {
			case OR:
				return list.length == 2 ? new LogEqOr2(pb, x, list) : new LogEqOr(pb, x, list);
			case AND:
				return list.length == 2 ? new LogEqAnd2(pb, x, list) : new LogEqAnd(pb, x, list);
			case XOR:
				return new LogEqXor(pb, x, list);
			case IFF:
				return new LogEqIff(pb, x, list);
			default:
				throw new AssertionError("unimplemented case");
			}
		}

		protected Variable x;

		protected Domain dx;

		public ReifLogic(Problem pb, Variable x, Variable[] list) {
			super(pb, pb.api.vars(x, list));
			this.x = x;
			this.dx = x.dom;
			control(list.length > 1 && !x.presentIn(list) && Variable.areAllInitiallyBoolean(scp), "Variables must be 01");
		}

		public static abstract class ReifLogic2 extends ReifLogic {

			protected Variable y, z;

			protected Domain dy, dz;

			public ReifLogic2(Problem pb, Variable x, Variable[] list) {
				super(pb, x, list);
				control(list.length == 2);
				this.y = list[0];
				this.z = list[1];
				this.dy = y.dom;
				this.dz = z.dom;
			}

			public static final class LogEqAnd2 extends ReifLogic2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == 0 ? t[1] == 0 || t[2] == 0 : t[1] == 1 && t[2] == 1;
				}

				public LogEqAnd2(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.first() == 1) // x = 1 => y = 1 and z = 1
						return dy.removeIfPresent(0) && dz.removeIfPresent(0) && entail();
					if (!dy.contains(1) || !dz.contains(1)) // y != 1 or z != 1 => x != 1
						return dx.removeIfPresent(1) && entail();
					// 0 is present in dx, and 1 in dy and 1 in dz; if present, (x,1) is supported
					if (dy.size() == 1 && dz.size() == 1) // y = 1 and z = 1 => x = 1
						return dx.remove(0) && entail();
					// (x,0) is supported
					if (dx.size() == 2)
						return true;
					// only 0 for x
					if (dy.size() == 2 && dz.size() == 2)
						return true;
					if (dy.size() == 2)
						return dy.remove(1) && entail();
					// dz.size() == 2
					return dz.remove(1) && entail();
				}
			}

			public static final class LogEqOr2 extends ReifLogic2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == 0 ? t[1] == 0 && t[2] == 0 : t[1] == 1 || t[2] == 1;
				}

				public LogEqOr2(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.last() == 0) // x = 0 => y = 0 and z = 0
						return dy.removeIfPresent(1) && dz.removeIfPresent(1) && entail();
					if (!dy.contains(0) || !dz.contains(0)) // y != 0 or z != 0 => x != 0
						return dx.removeIfPresent(0) && entail();
					// 1 is present in dx, and 0 in dy and 0 in dz; if present, (x,0) is supported
					if (dy.size() == 1 && dz.size() == 1) // y = 0 and z = 0 => x = 0
						return dx.remove(1) && entail();
					// (x,1) is supported
					if (dx.size() == 2)
						return true;
					// only 1 for x
					if (dy.size() == 2 && dz.size() == 2)
						return true;
					if (dy.size() == 2)
						return dy.remove(0) && entail();
					// dz.size() == 2
					return dz.remove(0) && entail();
				}
			}
		}

		public static abstract class ReifLogicn extends ReifLogic {

			protected Variable[] list;

			protected Variable sentinel1, sentinel2; // for variables of list supporting (x,0) if 'and', (x,1) if 'or'

			public ReifLogicn(Problem pb, Variable x, Variable[] list) {
				super(pb, x, list);
				this.list = list;
				control(list.length >= 2);
				this.sentinel1 = list[0]; // arbitrary sentinel
				this.sentinel2 = list[1]; // arbitrary sentinel
			}

			public static final class LogEqAnd extends ReifLogicn {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					if (t[0] == 0) { // if x = 0
						for (int i = 1; i < t.length; i++)
							if (t[i] == 0)
								return true;
						return false;
					}
					// x == 1
					for (int v : t)
						if (v == 0)
							return false;
					return true;
				}

				private Variable findSentinel(Variable other) {
					for (Variable y : list)
						if (y != other && y.dom.first() == 0)
							return y;
					return null;
				}

				public LogEqAnd(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				@Override
				public boolean runPropagator(Variable evt) {
					for (Variable y : list)
						if (y.dom.last() == 0)
							return dx.removeIfPresent(1) && entail(); // for some j, y_j = 0 => x = 0
					assert Stream.of(list).allMatch(y -> y.dom.last() == 1) : "1 should be present in the domain of every variable of the list";
					if (dx.first() == 1) { // x = 1 => y_j = 1 for every j
						for (Variable y : list)
							y.dom.removeIfPresent(0); // no possible inconsistency since 1 is also present
						return entail();
					}
					// it remains to check that (x,0) is supported (as well as any (y_j,0) equivalently)
					if (dx.last() == 0) { // if x=0, we need two valid sentinels
						if (sentinel1.dom.first() == 1) {
							Variable y = findSentinel(sentinel2);
							if (y == null)
								return sentinel2.dom.remove(1) && entail();
							sentinel1 = y;
						}
						if (sentinel2.dom.first() == 1) {
							Variable y = findSentinel(sentinel1);
							if (y == null)
								return sentinel1.dom.remove(1) && entail();
							sentinel2 = y;
						}
						return true;
					}
					// we just need one sentinel
					if (sentinel1.dom.first() == 0 || sentinel2.dom.first() == 0)
						return true;
					for (Variable y : list)
						if (y.dom.first() == 0) {
							sentinel1 = y;
							return true;
						}
					return dx.remove(0) && entail();
				}
			}

			public static final class LogEqOr extends ReifLogicn {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					if (t[0] == 0) { // if x = 0
						for (int v : t)
							if (v == 1)
								return false;
						return true;
					}
					// x == 1
					for (int i = 1; i < t.length; i++)
						if (t[i] == 1)
							return true;
					return false;
				}

				private Variable findSentinel(Variable other) {
					for (Variable y : list)
						if (y != other && y.dom.last() == 1)
							return y;
					return null;
				}

				public LogEqOr(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				@Override
				public boolean runPropagator(Variable evt) {
					for (Variable y : list)
						if (y.dom.first() == 1)
							return dx.removeIfPresent(0) && entail(); // for some j, y_j = 1 => x = 1
					assert Stream.of(list).allMatch(y -> y.dom.first() == 0) : "0 should be present in the domain of every variable of the list";
					if (dx.last() == 0) { // x = 0 => y_j = 0 for every j
						for (Variable y : list)
							y.dom.removeIfPresent(1); // no possible inconsistency since 0 is also present
						return entail();
					}
					// it remains to check that (x,1) is supported (as well as any (y_j,1) equivalently)
					if (dx.first() == 1) { // if x=1, we need two valid sentinels
						if (sentinel1.dom.last() == 0) {
							Variable y = findSentinel(sentinel2);
							if (y == null)
								return sentinel2.dom.remove(0) && entail();
							sentinel1 = y;
						}
						if (sentinel2.dom.last() == 0) {
							Variable y = findSentinel(sentinel1);
							if (y == null)
								return sentinel1.dom.remove(0) && entail();
							sentinel2 = y;
						}
						return true;
					}
					// if dom(x) = 01, we just need one sentinel
					if (sentinel1.dom.last() == 1 || sentinel2.dom.last() == 1)
						return true;
					for (Variable y : list)
						if (y.dom.last() == 1) {
							sentinel1 = y;
							return true;
						}
					return dx.remove(1) && entail();
				}
			}

			public static final class LogEqXor extends ReifLogicn {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					int cnt = 0;
					for (int i = 1; i < t.length; i++)
						if (t[i] == 1)
							cnt++;
					return (t[0] == 1) == (cnt % 2 == 1);
				}

				private Variable findSentinel(Variable other) {
					for (Variable y : list)
						if (y != other && y.dom.size() == 2)
							return y;
					return null;
				}

				public LogEqXor(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				private int toBeRemoved(Variable sentinel) {
					int cnt = 0;
					for (Variable z : list)
						if (z != sentinel && z.dom.single() == 1)
							cnt++;
					return dx.first() == 0 ? (cnt % 2 == 0 ? 1 : 0) : (cnt % 2 == 0 ? 0 : 1);
				}

				@Override
				public boolean runPropagator(Variable evt) {
					if (dx.size() == 2) {
						// only one sentinel is necessary for having AC
						if (sentinel1.dom.size() == 2 || sentinel2.dom.size() == 2)
							return true;
						Variable y = findSentinel(sentinel2);
						if (y == null) {
							int cnt = 0;
							for (Variable z : list)
								if (z.dom.single() == 1)
									cnt++;
							int a = cnt % 2 == 0 ? 1 : 0;
							return dx.remove(a) && entail();
						}
						sentinel1 = y;
						return true;
					}
					// if x=0 or x=1, we need two valid sentinels
					if (sentinel1.dom.size() == 1) {
						Variable y = findSentinel(sentinel2);
						if (y == null) {
							int a = toBeRemoved(sentinel2);
							return sentinel2.dom.removeIfPresent(a) && entail();
						}
						sentinel1 = y;
					}
					assert sentinel1 != sentinel2;
					if (sentinel2.dom.size() == 1) {
						Variable y = findSentinel(sentinel1);
						if (y == null) {
							int a = toBeRemoved(sentinel1);
							return sentinel1.dom.removeIfPresent(a) && entail();
						}
						sentinel2 = y;
					}
					return true;
				}
			}

			public static final class LogEqIff extends ReifLogicn {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					int first = t[1], i = 2;
					for (; i < t.length; i++)
						if (t[i] != first)
							break;
					return (t[0] == 1) == (i == t.length);
				}

				private Variable findSentinel(Variable other, int a) {
					for (Variable y : list)
						if (y != other && y.dom.contains(a))
							return y;
					return null;
				}

				public LogEqIff(Problem pb, Variable x, Variable[] list) {
					super(pb, x, list);
				}

				@Override
				public boolean runPropagator(Variable evt) {
					if (dx.size() == 2) {
						boolean sing0 = false, sing1 = false, size2 = false;
						for (Variable y : list) {
							if (y.dom.size() == 2)
								size2 = true;
							else if (y.dom.first() == 0) { // y=0
								if (sing1)
									return dx.remove(1) & entail();
								sing0 = true;
							} else { // y=1
								if (sing0)
									return dx.remove(1) & entail();
								sing1 = true;
							}
						}
						if (!size2)
							return dx.remove(0) & entail(); // because all assigned to 0 or to 1 (in list)
					} else if (dx.first() == 0) { // x=0 (so, we must have both 0 and 1 assigned)
						// we use sentinel1 for a domain with 0 present and sentinel2 for a domain with 1 present
						if (!sentinel1.dom.contains(0)) {
							Variable y = findSentinel(sentinel2, 0);
							if (y == null)
								return sentinel2.dom.reduceTo(0) && entail(); // may fail if 0 is not present
							sentinel1 = y;
						}
						if (!sentinel2.dom.contains(1)) {
							Variable y = findSentinel(sentinel1, 1);
							if (y == null)
								return sentinel1.dom.reduceTo(1) && entail();
							sentinel2 = y;
						}
						if (sentinel1.dom.size() == 2 && sentinel2.dom.size() == 2)
							return true;
						if (sentinel1.dom.size() == 2 && findSentinel(sentinel1, 0) == null)
							sentinel1.dom.reduceTo(0); // no possible failure here
						if (sentinel2.dom.size() == 2 && findSentinel(sentinel2, 1) == null)
							sentinel2.dom.reduceTo(1); // no possible failure here
						if (sentinel1.dom.size() == 1 && sentinel2.dom.size() == 1)
							return entail();
					} else {
						// x=1 (so we must have all variables of list assigned to either 0 or 1)
						for (Variable y : list) {
							if (y.dom.size() == 1) {
								int a = y.dom.first();
								// we must set all variables of list to a
								for (Variable z : list)
									if (z != y && z.dom.reduceTo(a) == false)
										return false;
								return entail();
							}
						}
					}
					return true;
				}
			}
		}
	}
}
