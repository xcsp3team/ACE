/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import static org.xcsp.common.Types.TypeConditionOperatorSet.NOTIN;
import static org.xcsp.common.Types.TypeOperatorRel.GT;
import static org.xcsp.common.Types.TypeOperatorRel.LT;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class CtrPrimitiveBinary extends CtrPrimitive implements TagGACGuaranteed {

	protected final Variable x, y;

	protected final Domain dx, dy;

	public CtrPrimitiveBinary(Problem pb, Variable x, Variable y) {
		super(pb, pb.api.vars(x, y));
		this.x = x;
		this.y = y;
		this.dx = x.dom;
		this.dy = y.dom;
	}

	public static class Disjonctive extends CtrPrimitiveBinary {

		private final int kx, ky;

		@Override
		public boolean checkValues(int[] t) {
			return t[0] + kx <= t[1] || t[1] + ky <= t[0];
		}

		@Override
		public Boolean isSymmetric() {
			return kx == ky;
		}

		public Disjonctive(Problem pb, Variable x, int kx, Variable y, int ky) {
			super(pb, x, y);
			this.kx = kx;
			this.ky = ky;
			defineKey(kx, ky);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int start = dy.lastValue() - kx + 1;
			int stop = dy.firstValue() + ky;
			if (start < stop && dx.removeValues(TypeConditionOperatorSet.IN, start, stop) == false)
				return false;
			start = dx.lastValue() - ky + 1;
			stop = dx.firstValue() + kx;
			if (start < stop && dy.removeValues(TypeConditionOperatorSet.IN, start, stop) == false)
				return false;
			return true;
		}
	}

	public static abstract class CtrPrimitiveBinaryAdd extends CtrPrimitiveBinary {

		public static CtrAlone buildFrom(Problem pb, Variable x, int k, TypeConditionOperatorRel op, Variable y) {
			if (op == TypeConditionOperatorRel.LT)
				return pb.addCtr(new LE(pb, x, k + 1, y));
			if (op == TypeConditionOperatorRel.LE)
				return pb.addCtr(new LE(pb, x, k, y));
			if (op == TypeConditionOperatorRel.GE)
				return pb.addCtr(new GE(pb, x, k, y));
			if (op == TypeConditionOperatorRel.GT)
				return pb.addCtr(new GE(pb, x, k - 1, y));
			if (op == TypeConditionOperatorRel.EQ) {
				return pb.extension(XNodeParent.eq(XNodeParent.add(x, k), y));
				// return pb.addCtr(new EQ(pb, x, k, y));
			}
			Kit.control(op == TypeConditionOperatorRel.NE, () -> "pb");
			return pb.addCtr(new NE(pb, x, k, y));
		}

		protected final int k;

		public CtrPrimitiveBinaryAdd(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
		}

		public static class LE extends CtrPrimitiveBinaryAdd implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + k <= t[1];
			}

			public LE(Problem pb, Variable x, int k, Variable y) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValues(GT, dy.lastValue() - k) && dy.removeValues(LT, dx.firstValue() + k);
			}
		}

		public static class GE extends CtrPrimitiveBinaryAdd implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + k >= t[1];
			}

			public GE(Problem pb, Variable x, int k, Variable y) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValues(LT, dy.firstValue() - k) && dy.removeValues(GT, dx.lastValue() + k);
			}
		}

		public static final class EQ extends CtrPrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + k == t[1];
			}

			public EQ(Problem pb, Variable x, int k, Variable y) {
				super(pb, x, y, k);
			}

			@Override
			public Boolean isSymmetric() {
				return k == 0;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.removeValues(NOTIN, dy, -k) == false)
					return false;
				assert dx.size() <= dy.size();
				if (dy.size() == dx.size())
					return true;
				boolean consistent = dy.removeValues(NOTIN, dx, k);
				assert consistent;
				return true;
			}
		}

		public static final class NE extends CtrPrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + k != t[1];
			}

			public NE(Problem pb, Variable x, int k, Variable y) {
				super(pb, x, y, k);
			}

			@Override
			public Boolean isSymmetric() {
				return k == 0;
			}

			@Override
			public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable x, int a) {
				return 1;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1 && dy.removeValue(dx.uniqueValue() + k, false) == false)
					return false;
				if (dy.size() == 1 && dx.removeValue(dy.uniqueValue() - k, false) == false)
					return false;
				return true;
			}
		}
	}

	public static abstract class CtrPrimitiveBinaryDist extends CtrPrimitiveBinary implements TagSymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			if (op == TypeConditionOperatorRel.LT)
				return pb.extension(XNodeParent.lt(XNodeParent.dist(x, y), k));
			if (op == TypeConditionOperatorRel.LE)
				return pb.extension(XNodeParent.le(XNodeParent.dist(x, y), k));
			if (op == TypeConditionOperatorRel.GE)
				return pb.addCtr(new DistGE(pb, x, y, k));
			if (op == TypeConditionOperatorRel.GT)
				return pb.addCtr(new DistGE(pb, x, y, k + 1));
			if (op == TypeConditionOperatorRel.EQ)
				return pb.extension(XNodeParent.eq(XNodeParent.dist(x, y), k));
			Kit.control(op == TypeConditionOperatorRel.NE, () -> "pb");
			return pb.addCtr(new DistNE(pb, x, y, k));
		}

		protected final int k;

		public CtrPrimitiveBinaryDist(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
			Utilities.control(k >= 0, "k should be positive");
		}

		public static class DistGE extends CtrPrimitiveBinaryDist { // code similar to Disjunctive

			@Override
			public boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) >= k; // equivalent to t[0] + k <= t[1] || t[1] + k <= t[0];
			}

			public DistGE(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				int start = dy.lastValue() - k + 1;
				int stop = dy.firstValue() + k;
				if (start < stop && dx.removeValues(TypeConditionOperatorSet.IN, start, stop) == false)
					return false;
				start = dx.lastValue() - k + 1;
				stop = dx.firstValue() + k;
				if (start < stop && dy.removeValues(TypeConditionOperatorSet.IN, start, stop) == false)
					return false;
				return true;
			}
		}

		public static class DistNE extends CtrPrimitiveBinaryDist {

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) != k;
			}

			public DistNE(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			private boolean revise(Domain dom1, Domain dom2) {
				if (dom1.size() == 1)
					return dom2.removeValue(dom1.uniqueValue() - k, false) && dom2.removeValue(dom1.uniqueValue() + k, false);
				if (dom1.size() == 2 && dom1.lastValue() - dom1.firstValue() == 2 * k)
					return dom2.removeValue(dom1.lastValue() - k, false);
				return true;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy) && revise(dy, dx);
			}
		}
	}

}

// public static class LT extends CtrPrimitiveBinaryCst implements TagUnsymmetric {
//
// @Override
// public final boolean checkValues(int[] t) {
// return t[0] + k < t[1];
// }
//
// public LT(Problem pb, Variable x, int k, Variable y) {
// super(pb, x, y, k);
// }
//
// @Override
// public boolean runPropagator(Variable dummy) {
// return dx.removeValues(GT, dy.lastValue() - 1 - k) && dy.removeValues(LT, dx.firstValue() + 1 + k);
// }
// }

// public static class GT extends CtrPrimitiveBinaryCst implements TagUnsymmetric {
//
// @Override
// public final boolean checkValues(int[] t) {
// return t[0] + k > t[1];
// }
//
// public GT(Problem pb, Variable x, int k, Variable y) {
// super(pb, x, y, k);
// }
//
// @Override
// public boolean runPropagator(Variable dummy) {
// return dx.removeValues(LT, dy.firstValue() + 1 - k) && dy.removeValues(GT, dx.lastValue() - 1 + k);
// }
// }
