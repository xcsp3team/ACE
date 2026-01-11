/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.intension;

import static utility.Kit.control;

import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import variables.Domain;
import variables.Variable;

/**
 * This class contains some propagators for quaternary primitive constraints. <br />
 * For the moment, it only concerns two disjonctive forms.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Primitive4 extends Primitive implements TagAC, TagCallCompleteFiltering {

	public Primitive4(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	public static final class DisjonctiveVar extends Primitive4 {

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

	public static final class Disjonctive2Cst extends Primitive4 {

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

	public static final class Disjonctive2Mix extends Primitive implements TagAC, TagCallCompleteFiltering {

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

	public static final class Disjonctive2Var extends Primitive implements TagAC, TagCallCompleteFiltering {

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

	public static final class DblDiff extends Primitive4 {

		private Domain dom0, dom1, dom2, dom3;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] != t[1] || t[2] != t[3]; // x1 != x2 or y1 != y2
		}

		public DblDiff(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
			super(pb, new Variable[] { x1, x2, y1, y2 });
			this.dom0 = x1.dom;
			this.dom1 = x2.dom;
			this.dom2 = y1.dom;
			this.dom3 = y2.dom;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			boolean s0 = dom0.size() == 1, s1 = dom1.size() == 1, s2 = dom2.size() == 1, s3 = dom3.size() == 1;
			boolean b1 = s0 && s1;
			boolean b2 = s2 && s3;
			if (!b1 && !b2)
				return true;
			if (b1 && b2)// all 4 variables assigned
				return dom0.singleValue() != dom1.singleValue() || dom2.singleValue() != dom3.singleValue() ? entail() : dummy.dom.fail();
			if (b1) {
				if (dom0.singleValue() != dom1.singleValue())
					return entail();
				if (s2)
					return dom3.removeValueIfPresent(dom2.singleValue()) && entail(); // no inconsistency possible here
				if (s3)
					return dom2.removeValueIfPresent(dom3.singleValue()) && entail(); // no inconsistency possible here
				return true;
			}
			if (b2) {
				if (dom2.singleValue() != dom3.singleValue())
					return entail();
				if (s0)
					return dom1.removeValueIfPresent(dom0.singleValue()) && entail(); // no inconsistency possible here
				if (s1)
					return dom0.removeValueIfPresent(dom1.singleValue()) && entail(); // no inconsistency possible here
				return true;
			}
			return true;
		}
	}

	public static final class DblDiff2 extends Primitive4 { // old propagator (less efficient in time)

		/** Two sentinels for tracking the presence of two non singleton domains. */
		private int sentinel1, sentinel2;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] != t[1] || t[2] != t[3]; // x1 != x2 or y1 != y2
		}

		public DblDiff2(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
			super(pb, new Variable[] { x1, x2, y1, y2 });
			sentinel1 = 0;
			sentinel2 = 1;
		}

		private int findAnotherSentinel() {
			for (int i = 0; i < scp.length; i++) {
				if (i == sentinel1 || i == sentinel2)
					continue;
				if (doms[i].size() > 1)
					return i;
			}
			return -1;
		}

		private boolean justOneSentinel(int sentinel) {
			assert (doms[0].size() > 1 ? 1 : 0) + (doms[1].size() > 1 ? 1 : 0) + (doms[2].size() > 1 ? 1 : 0) + (doms[3].size() > 1 ? 1 : 0) <= 1;
			Domain dom = doms[sentinel];
			if (dom.size() == 1) // all 4 variables assigned
				return doms[0].singleValue() != doms[1].singleValue() || doms[2].singleValue() != doms[3].singleValue() ? entail() : dom.fail();
			if (sentinel < 2) {
				if (doms[2].singleValue() != doms[3].singleValue())
					return entail();
				int v = doms[sentinel == 0 ? 1 : 0].singleValue();
				return dom.removeValueIfPresent(v) && entail(); // no inconsistency possible here
			} else {
				if (doms[0].singleValue() != doms[1].singleValue())
					return entail();
				int v = doms[sentinel == 2 ? 3 : 2].singleValue();
				return dom.removeValueIfPresent(v) && entail(); // no inconsistency possible here
			}
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (doms[sentinel1].size() == 1) {
				int sentinel = findAnotherSentinel();
				if (sentinel == -1)
					return justOneSentinel(sentinel2);
				else
					sentinel1 = sentinel;
			}
			if (doms[sentinel2].size() == 1) {
				int sentinel = findAnotherSentinel();
				if (sentinel == -1)
					return justOneSentinel(sentinel1);
				else
					sentinel2 = sentinel;
			}
			return true;
		}
	}
}
