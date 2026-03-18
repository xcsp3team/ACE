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

import constraints.ConstraintSpecific;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagPrimitive;
import problem.Problem;
import propagation.AC;
import propagation.AC.TypeFilteringResult;
import variables.Domain;
import variables.Variable;

/**
 * This class contains some propagators for quaternary primitive constraints. <br />
 * For the moment, it only concerns two disjonctive forms.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Primitive4 extends ConstraintSpecific implements TagAC, TagCallCompleteFiltering, TagPrimitive {

	protected Domain dx1, dx2, dy1, dy2;

	public Primitive4(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
		super(pb, new Variable[] { x1, x2, y1, y2 });
		this.dx1 = x1.dom;
		this.dx2 = x2.dom;
		this.dy1 = y1.dom;
		this.dy2 = y2.dom;
	}

	public static final class DblDiff extends Primitive4 {
		// new propagator (seems to be 5-10% more efficient in time - see e.g. ExaminationTimetabling1-merged-D1-1-16.xml)

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] != t[1] || t[2] != t[3]; // x1 != x2 or y1 != y2
		}

		public DblDiff(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
			super(pb, x1, x2, y1, y2);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			boolean s0 = dx1.size() == 1, s1 = dx2.size() == 1, s2 = dy1.size() == 1, s3 = dy2.size() == 1;
			boolean b1 = s0 && s1;
			boolean b2 = s2 && s3;
			if (!b1 && !b2)
				return true;
			if (b1 && b2)// all 4 variables assigned
				return dx1.singleValue() != dx2.singleValue() || dy1.singleValue() != dy2.singleValue() ? entail() : dummy.dom.fail();
			if (b1) {
				if (dx1.singleValue() != dx2.singleValue())
					return entail();
				if (s2)
					return dy2.removeValueIfPresent(dy1.singleValue()) && entail(); // no inconsistency possible here
				if (s3)
					return dy1.removeValueIfPresent(dy2.singleValue()) && entail(); // no inconsistency possible here
				return true;
			}
			if (b2) {
				if (dy1.singleValue() != dy2.singleValue())
					return entail();
				if (s0)
					return dx2.removeValueIfPresent(dx1.singleValue()) && entail(); // no inconsistency possible here
				if (s1)
					return dx1.removeValueIfPresent(dx2.singleValue()) && entail(); // no inconsistency possible here
				return true;
			}
			return true;
		}
	}

	public static final class DistDistNE extends Primitive4 {

		private static final int NO = Integer.MAX_VALUE;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return Math.abs(t[0] - t[1]) != Math.abs(t[2] - t[3]); // |x1 - x2| != |y1 - y2|
		}

		public DistDistNE(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
			super(pb, x1, x2, y1, y2);
		}

		private int onlyOneRemaining(Domain d1, Domain d2) {
			if (d1.size() == 1) {
				if (d2.size() == 1)
					return Math.abs(d1.singleValue() - d2.singleValue());
				if (d2.size() == 2) {
					int dst = Math.abs(d1.singleValue() - d2.firstValue());
					if (dst == Math.abs(d1.singleValue() - d2.lastValue()))
						return dst;
				}
				return NO;
			}
			if (d2.size() == 1) {
				if (d1.size() == 2) {
					int dst = Math.abs(d2.singleValue() - d1.firstValue());
					if (dst == Math.abs(d2.singleValue() - d1.lastValue()))
						return dst;
				}
				return NO;
			}
			return NO;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int oneLeft = onlyOneRemaining(dx1, dx2), oneRight = onlyOneRemaining(dy1, dy2);
			if (oneLeft == NO && oneRight == NO)
				return true;
			if (oneLeft != NO && oneRight != NO)
				return oneLeft != oneRight ? entail() : dummy.dom.fail();
			if (oneLeft != NO) {
				TypeFilteringResult res = AC.enforceDistNE(dy1, dy2, oneLeft);
				if (res == TypeFilteringResult.ENTAIL)
					return entail();
				assert res == TypeFilteringResult.TRUE || res == TypeFilteringResult.FALSE; // FAIL not possible
				return res == TypeFilteringResult.TRUE;
			}
			assert oneRight != NO;
			TypeFilteringResult res = AC.enforceDistNE(dx1, dx2, oneRight);
			if (res == TypeFilteringResult.ENTAIL)
				return entail();
			assert res == TypeFilteringResult.TRUE || res == TypeFilteringResult.FALSE; // FAIL not possible
			return res == TypeFilteringResult.TRUE;
		}
	}
}
