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

	public Primitive4(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	public static final class DblDiff extends Primitive4 {
		// new propagator (seems to be 5-10% more efficient in time - see e.g. ExaminationTimetabling1-merged-D1-1-16.xml)

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

	public static final class DistDistNE extends Primitive4 {

		private static final int NO = Integer.MAX_VALUE;

		private Domain dom0, dom1, dom2, dom3;

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return Math.abs(t[0] - t[1]) != Math.abs(t[2] - t[3]); // |x1 - x2| != |y1 - y2|
		}

		public DistDistNE(Problem pb, Variable x1, Variable x2, Variable y1, Variable y2) {
			super(pb, new Variable[] { x1, x2, y1, y2 });
			this.dom0 = x1.dom;
			this.dom1 = x2.dom;
			this.dom2 = y1.dom;
			this.dom3 = y2.dom;
		}

		private int onlyOneLeft(Domain d1, Domain d2) {
			if (d1.size() == 1) {
				int v1 = d1.singleValue();
				if (d2.size() == 1)
					return Math.abs(v1 - d2.singleValue());
				if (d2.size() == 2 && Math.abs(v1 - d2.firstValue()) == Math.abs(v1 - d2.lastValue()))
					return Math.abs(v1 - d2.firstValue());
				return NO;
			}
			if (d2.size() == 1) {
				int v2 = d2.singleValue();
				assert d1.size() != 1;
				if (d1.size() == 2 && Math.abs(v2 - d1.firstValue()) == Math.abs(v2 - d1.lastValue()))
					return Math.abs(v2 - d1.firstValue());
				return NO;
			}
			return NO;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int oneLeft = onlyOneLeft(dom0, dom1), oneRight = onlyOneLeft(dom2, dom3);
			if (oneLeft == NO && oneRight == NO)
				return true;
			if (oneLeft != NO && oneRight != NO)
				return oneLeft != oneRight ? entail() : dummy.dom.fail();
			if (oneLeft != NO) {
				TypeFilteringResult res = AC.enforceDistNE(dom2, dom3, oneLeft);
				if (res == TypeFilteringResult.ENTAIL)
					return entail();
				assert res == TypeFilteringResult.TRUE || res == TypeFilteringResult.FALSE; // FAIL not possible
				return res == TypeFilteringResult.TRUE;
			}
			assert oneRight != NO;
			TypeFilteringResult res = AC.enforceDistNE(dom0, dom1, oneRight);
			if (res == TypeFilteringResult.ENTAIL)
				return entail();
			assert res == TypeFilteringResult.TRUE || res == TypeFilteringResult.FALSE; // FAIL not possible
			return res == TypeFilteringResult.TRUE;
		}
	}
}
