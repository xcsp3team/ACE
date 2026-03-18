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

import static propagation.AC.enforceLE;
import static utility.Kit.control;

import constraints.ConstraintSpecific;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotSymmetric;
import interfaces.Tags.TagPrimitive;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This class contains some propagators for disjonctive-like constraints.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Disjonctive extends ConstraintSpecific implements TagAC, TagCallCompleteFiltering, TagPrimitive {

	public Disjonctive(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	public static final class DisjonctiveVar extends Disjonctive {

		final Variable x1, x2, w1, w2;
		final Domain dx1, dx2, dw1, dw2;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] + t[2] <= t[1] || t[1] + t[3] <= t[0]; // x1+w1 <= x2 or x2+w2 <= x1
		}

		public DisjonctiveVar(Problem pb, Variable x1, Variable x2, Variable w1, Variable w2) {
			super(pb, new Variable[] { x1, x2, w1, w2 });
			this.x1 = x1;
			this.x2 = x2;
			this.w1 = w1;
			this.w2 = w2;
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dw1 = w1.dom;
			this.dw2 = w2.dom;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int min1 = dx1.firstValue() + dw1.firstValue(), min2 = dx2.firstValue() + dw2.firstValue();
			int max1 = dx2.lastValue() - dw1.firstValue(), max2 = dx1.lastValue() - dw2.firstValue();
			boolean b1 = min1 <= dx2.lastValue(), b2 = min2 <= dx1.lastValue();
			if (!b1 && !b2)
				return false;
			if (!b2) // we enforce the first part
				return dx2.removeValuesLT(min1) && dx1.removeValuesGT(max1) && dw1.removeValuesGT(dx2.lastValue() - dx1.firstValue());
			if (!b1) // we enforce the second part
				return dx1.removeValuesLT(min2) && dx2.removeValuesGT(max2) && dw2.removeValuesGT(dx1.lastValue() - dx2.firstValue());
			return dx1.removeValuesInRange(max1 + 1, min2) && dx2.removeValuesInRange(max2 + 1, min1);
		}
	}

	public static final class Disjonctive2Cst extends Disjonctive {

		final int w1, w2, h1, h2;

		final Domain dx1, dx2, dy1, dy2;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] + w1 <= t[1] || t[1] + w2 <= t[0] || t[2] + h1 <= t[3] || t[3] + h2 <= t[2];
			// x1+w1 <= x2 or x2+w2 <= x1 or y1+h1 <= y2 or y2+h2 <= y1
		}

		public Disjonctive2Cst(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, int w1, int w2, int h1, int h2) {
			super(pb, new Variable[] { x1, x2, y1, y2 });
			control(scp.length == 4);
			this.w1 = w1;
			this.w2 = w2;
			this.h1 = h1;
			this.h2 = h2;
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			defineKey(w1, w2, h1, h2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dx1.lastValue() + w1 <= dx2.firstValue() || dx2.lastValue() + w2 <= dx1.firstValue())
				return entail();
			if (dy1.lastValue() + h1 <= dy2.firstValue() || dy2.lastValue() + h2 <= dy1.firstValue())
				return entail();
			int minx1 = dx1.firstValue() + w1, minx2 = dx2.firstValue() + w2;
			int miny1 = dy1.firstValue() + h1, miny2 = dy2.firstValue() + h2;
			boolean bx1 = minx1 <= dx2.lastValue(), bx2 = minx2 <= dx1.lastValue();
			boolean by1 = miny1 <= dy2.lastValue(), by2 = miny2 <= dy1.lastValue();
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

	public static final class Disjonctive2Mix extends Disjonctive {

		final int h1, h2;

		final Domain dx1, dx2, dy1, dy2, dw1, dw2;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] + t[4] <= t[1] || t[1] + t[5] <= t[0] || t[2] + h1 <= t[3] || t[3] + h2 <= t[2];
			// x1+w1 <= x2 or x2+w2 <= x1 or y1+h1 <= y2 or y2+h2 <= y1
		}

		public Disjonctive2Mix(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, Variable w1, Variable w2, int h1, int h2) {
			super(pb, new Variable[] { x1, x2, y1, y2, w1, w2 });
			control(scp.length == 6);
			this.h1 = h1;
			this.h2 = h2;
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			this.dw1 = w1.dom;
			this.dw2 = w2.dom;
			defineKey(h1, h2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dx1.lastValue() + dw1.lastValue() <= dx2.firstValue() || dx2.lastValue() + dw2.lastValue() <= dx1.firstValue())
				return entail();
			if (dy1.lastValue() + h1 <= dy2.firstValue() || dy2.lastValue() + h2 <= dy1.firstValue())
				return entail();
			int minx1 = dx1.firstValue() + dw1.firstValue(), minx2 = dx2.firstValue() + dw2.firstValue();
			int miny1 = dy1.firstValue() + h1, miny2 = dy2.firstValue() + h2;
			boolean bx1 = minx1 <= dx2.lastValue(), bx2 = minx2 <= dx1.lastValue();
			boolean by1 = miny1 <= dy2.lastValue(), by2 = miny2 <= dy1.lastValue();
			boolean bx = bx1 || bx2, by = by1 || by2;
			if (bx && by)
				return true;
			if (!bx && !by)
				return false;
			if (bx) {
				if (dx1.removeValuesInRange(dx2.lastValue() - dw1.firstValue() + 1, minx2) == false)
					return false;
				if (dx2.removeValuesInRange(dx1.lastValue() - dw2.firstValue() + 1, minx1) == false)
					return false;
				if (!bx1)
					if (dw2.removeValuesGT(dx1.lastValue() - dx2.firstValue()) == false)
						return false;
				if (!bx2)
					if (dw1.removeValuesGT(dx2.lastValue() - dx1.firstValue()) == false)
						return false;
				return true;
			} else
				return dy1.removeValuesInRange(dy2.lastValue() - h1 + 1, miny2) && dy2.removeValuesInRange(dy1.lastValue() - h2 + 1, miny1);
		}
	}

	public static final class Disjonctive2Var extends Disjonctive {

		final Domain dx1, dx2, dy1, dy2, dw1, dw2, dh1, dh2;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] + t[4] <= t[1] || t[1] + t[5] <= t[0] || t[2] + t[6] <= t[3] || t[3] + t[7] <= t[2];
			// x1+w1 <= x2 or x2+w2 <= x1 or y1+h1 <= y2 or y2+h2 <= y1
		}

		public Disjonctive2Var(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2, Variable w1, Variable w2, Variable h1, Variable h2) {
			super(pb, new Variable[] { x1, x2, y1, y2, w1, w2, h1, h2 });
			control(scp.length == 8);
			this.dx1 = x1.dom;
			this.dx2 = x2.dom;
			this.dy1 = y1.dom;
			this.dy2 = y2.dom;
			this.dw1 = w1.dom;
			this.dw2 = w2.dom;
			this.dh1 = h1.dom;
			this.dh2 = h2.dom;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dx1.lastValue() + dw1.lastValue() <= dx2.firstValue() || dx2.lastValue() + dw2.lastValue() <= dx1.firstValue())
				return entail();
			if (dy1.lastValue() + dh1.lastValue() <= dy2.firstValue() || dy2.lastValue() + dh2.lastValue() <= dy1.firstValue())
				return entail();
			int minx1 = dx1.firstValue() + dw1.firstValue(), minx2 = dx2.firstValue() + dw2.firstValue();
			int miny1 = dy1.firstValue() + dh1.firstValue(), miny2 = dy2.firstValue() + dh2.firstValue();
			boolean bx1 = minx1 <= dx2.lastValue(), bx2 = minx2 <= dx1.lastValue();
			boolean by1 = miny1 <= dy2.lastValue(), by2 = miny2 <= dy1.lastValue();
			boolean bx = bx1 || bx2, by = by1 || by2;
			if (bx && by)
				return true;
			if (!bx && !by)
				return false;
			if (bx) {
				if (dx1.removeValuesInRange(dx2.lastValue() - dw1.firstValue() + 1, minx2) == false)
					return false;
				if (dx2.removeValuesInRange(dx1.lastValue() - dw2.firstValue() + 1, minx1) == false)
					return false;
				if (!bx1)
					if (dw2.removeValuesGT(dx1.lastValue() - dx2.firstValue()) == false)
						return false;
				if (!bx2)
					if (dw1.removeValuesGT(dx2.lastValue() - dx1.firstValue()) == false)
						return false;
				return true;
			} else {
				if (dy1.removeValuesInRange(dy2.lastValue() - dh1.firstValue() + 1, miny2) == false)
					return false;
				if (dy2.removeValuesInRange(dy1.lastValue() - dh2.firstValue() + 1, miny1) == false)
					return false;
				if (!by1)
					if (dh2.removeValuesGT(dy1.lastValue() - dy2.firstValue()) == false)
						return false;
				if (!by2)
					if (dh1.removeValuesGT(dy2.lastValue() - dy1.firstValue()) == false)
						return false;
				return true;
				// return dy1.removeValuesInRange(dy2.lastValue() - h1 + 1, miny2) && dy2.removeValuesInRange(dy1.lastValue() - h2 + 1, miny1);
			}
		}
	}

	/**********************************************************************************************
	 *** Reified forms
	 *********************************************************************************************/

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

	public static final class Disjonctive2Reified2Cst extends ConstraintSpecific implements TagNotAC, TagCallCompleteFiltering, TagNotSymmetric, TagPrimitive {
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

	public static final class Disjonctive2ReifiedVar extends ConstraintSpecific implements TagNotAC, TagCallCompleteFiltering, TagNotSymmetric, TagPrimitive {
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
}
