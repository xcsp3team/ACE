/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorSet.NOTIN;
import static org.xcsp.common.predicates.XNodeParent.add;
import static org.xcsp.common.predicates.XNodeParent.dist;
import static org.xcsp.common.predicates.XNodeParent.eq;
import static org.xcsp.common.predicates.XNodeParent.le;
import static org.xcsp.common.predicates.XNodeParent.lt;
import static org.xcsp.common.predicates.XNodeParent.sub;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import interfaces.TagUnsymmetric;
import problem.Problem;
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
			if (start < stop && dx.removeValuesInRange(start, stop) == false)
				return false;
			start = dx.lastValue() - ky + 1;
			stop = dx.firstValue() + kx;
			if (start < stop && dy.removeValuesInRange(start, stop) == false)
				return false;
			return true;
		}
	}

	// ************************************************************************
	// ***** Classes for x - y <op> k (CtrPrimitiveBinarySub)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinarySub extends CtrPrimitiveBinary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			assert op != null;
			if (op == LT)
				return pb.addCtr(new SubLE2(pb, x, y, k - 1));
			if (op == LE)
				return pb.addCtr(new SubLE2(pb, x, y, k));
			if (op == GE)
				return pb.addCtr(new SubGE2(pb, x, y, k));
			if (op == GT)
				return pb.addCtr(new SubGE2(pb, x, y, k + 1));
			if (op == EQ) {
				return pb.extension(eq(sub(x, y), k));
				// return pb.addCtr(new SubEQ2(pb, x, y, k));
			}
			return pb.addCtr(new SubNE2(pb, x, y, k));
		}

		protected final int k;

		public CtrPrimitiveBinarySub(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
		}

		public static class SubLE2 extends CtrPrimitiveBinarySub implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] <= k;
			}

			public SubLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesGreaterThan(dy.lastValue() + k) && dy.removeValuesLessThan(dx.firstValue() - k);
			}
		}

		public static class SubGE2 extends CtrPrimitiveBinarySub implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] >= k;
			}

			public SubGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesLessThan(dy.firstValue() + k) && dy.removeValuesGreaterThan(dx.lastValue() - k);
			}
		}

		public static final class SubEQ2 extends CtrPrimitiveBinarySub {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] == k;
			}

			public SubEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public Boolean isSymmetric() {
				return k == 0;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.removeValues(NOTIN, dy, k) == false)
					return false;
				assert dx.size() <= dy.size();
				if (dy.size() == dx.size())
					return true;
				boolean consistent = dy.removeValues(NOTIN, dx, -k);
				assert consistent;
				return true;
			}
		}

		public static final class SubNE2 extends CtrPrimitiveBinarySub {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] != k;
			}

			public SubNE2(Problem pb, Variable x, Variable y, int k) {
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
				if (dx.size() == 1 && dy.removeValue(dx.uniqueValue() - k, false) == false)
					return false;
				if (dy.size() == 1 && dx.removeValue(dy.uniqueValue() + k, false) == false)
					return false;
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x + y <op> k (CtrPrimitiveBinaryAdd)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryAdd extends CtrPrimitiveBinary implements TagSymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			assert op != null;
			if (op == LT)
				return pb.addCtr(new AddLE2(pb, x, y, k - 1));
			if (op == LE)
				return pb.addCtr(new AddLE2(pb, x, y, k));
			if (op == GE)
				return pb.addCtr(new AddGE2(pb, x, y, k));
			if (op == GT)
				return pb.addCtr(new AddGE2(pb, x, y, k + 1));
			if (op == EQ)
				return pb.extension(eq(add(x, y), k));
			return pb.addCtr(new AddNE2(pb, x, y, k));
		}

		protected final int k;

		public CtrPrimitiveBinaryAdd(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
		}

		public static class AddLE2 extends CtrPrimitiveBinaryAdd implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] <= k;
			}

			public AddLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesGreaterThan(k - dy.firstValue()) && dy.removeValuesGreaterThan(k - dx.firstValue());
			}
		}

		public static class AddGE2 extends CtrPrimitiveBinaryAdd implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] >= k;
			}

			public AddGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesLessThan(k - dy.lastValue()) && dy.removeValuesLessThan(k - dx.lastValue());
			}
		}

		public static final class AddNE2 extends CtrPrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] != k;
			}

			public AddNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable x, int a) {
				return 1;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1 && dy.removeValue(k - dx.uniqueValue(), false) == false)
					return false;
				if (dy.size() == 1 && dx.removeValue(k - dy.uniqueValue(), false) == false)
					return false;
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for |x - y| <op> k (CtrPrimitiveBinaryDist)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryDist extends CtrPrimitiveBinary implements TagSymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			assert op != null;
			if (op == LT)
				return pb.extension(lt(dist(x, y), k));
			if (op == LE)
				return pb.extension(le(dist(x, y), k));
			if (op == GE)
				return pb.addCtr(new DistGE2(pb, x, y, k));
			if (op == GT)
				return pb.addCtr(new DistGE2(pb, x, y, k + 1));
			if (op == EQ)
				return pb.extension(eq(dist(x, y), k));
			return pb.addCtr(new DistNE2(pb, x, y, k));
		}

		protected final int k;

		public CtrPrimitiveBinaryDist(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
			Utilities.control(k >= 0, "k should be positive");
		}

		public static class DistGE2 extends CtrPrimitiveBinaryDist { // code similar to Disjunctive

			@Override
			public boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) >= k; // equivalent to disjunctive: t[0] + k <= t[1] || t[1] + k <= t[0];
			}

			public DistGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				int start = dy.lastValue() - k + 1;
				int stop = dy.firstValue() + k;
				if (start < stop && dx.removeValuesInRange(start, stop) == false)
					return false;
				start = dx.lastValue() - k + 1;
				stop = dx.firstValue() + k;
				if (start < stop && dy.removeValuesInRange(start, stop) == false)
					return false;
				return true;
			}
		}

		public static class DistNE2 extends CtrPrimitiveBinaryDist {

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) != k;
			}

			public DistNE2(Problem pb, Variable x, Variable y, int k) {
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

	public static abstract class CtrPrimitiveBinaryLog extends CtrPrimitiveBinary implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			assert op != null;
			if (op == LT)
				return pb.addCtr(new LogLE2(pb, x, y, k - 1));
			if (op == LE)
				return pb.addCtr(new LogLE2(pb, x, y, k));
			if (op == GE)
				return pb.addCtr(new LogGE2(pb, x, y, k));
			if (op == GT)
				return pb.addCtr(new LogGE2(pb, x, y, k + 1));
			if (op == EQ)
				pb.addCtr(new LogEQ2(pb, x, y, k));
			return pb.addCtr(new LogNE2(pb, x, y, k));
		}

		protected final int k;

		public CtrPrimitiveBinaryLog(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
			Utilities.control(dx.is01(), "The first variable should be of type 01");
		}

		public static class LogLE2 extends CtrPrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] <= k);
			}

			public LogLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.lastValue() <= k && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.firstValue() > k && dx.remove(1) == false)
					return false;
				if (dx.first() != 0 && dy.lastValue() > k && dy.removeValuesGreaterThan(k) == false)
					return false;
				if (dx.last() != 1 && dy.firstValue() <= k && dy.removeValuesLessThanOrEqual(k) == false)
					return false;
				return true;
			}
		}

		public static class LogGE2 extends CtrPrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] >= k);
			}

			public LogGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.firstValue() >= k && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.lastValue() < k && dx.remove(1) == false)
					return false;
				if (dx.first() != 0 && dy.firstValue() < k && dy.removeValuesLessThan(k) == false)
					return false;
				if (dx.last() != 1 && dy.lastValue() >= k && dy.removeValuesGreaterThanOrEqual(k) == false)
					return false;
				return true;
			}
		}

		public static class LogEQ2 extends CtrPrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] == k);
			}

			public LogEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (!dy.isPresentValue(k)) {
					if (dx.last() == 1 && dx.remove(1) == false)
						return false;
				} else if (dy.size() == 1) {
					if (dx.first() == 0 && dx.remove(0) == false)
						return false;
				}
				if (dx.size() == 1) {
					if (dx.first() == 0 && dy.removeValue(k, false) == false)
						return false;
					if (dx.first() == 1 && dy.reduceToValue(k) == false)
						return false;
				}
				return true;
			}
		}

		public static class LogNE2 extends CtrPrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] != k);
			}

			public LogNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (!dy.isPresentValue(k)) {
					if (dx.first() == 0 && dx.remove(0) == false)
						return false;
				} else if (dy.size() == 1) {
					if (dx.last() == 1 && dx.remove(1) == false)
						return false;
				}
				if (dx.size() == 1) {
					if (dx.first() == 0 && dy.reduceToValue(k) == false)
						return false;
					if (dx.first() == 1 && dy.removeValue(k, false) == false)
						return false;
				}
				return true;
			}
		}

	}

	public static abstract class CtrPrimitiveTernaryLog extends CtrPrimitiveTernary implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			// assert op != null;
			// if (op == LT)
			// return pb.addCtr(new LogLE2(pb, x, y, k - 1));
			// if (op == LE)
			// return pb.addCtr(new LogLE2(pb, x, y, k));
			// if (op == GE)
			// return pb.addCtr(new LogGE2(pb, x, y, k));
			// if (op == GT)
			// return pb.addCtr(new LogGE2(pb, x, y, k + 1));
			// if (op == EQ)
			// pb.addCtr(new LogEQ2(pb, x, y, k));
			// return pb.addCtr(new LogNE2(pb, x, y, k));
			return null;
		}

		public CtrPrimitiveTernaryLog(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
			Utilities.control(domx.is01(), "The first variable should be of type 01");
		}

		public static class LogLE3 extends CtrPrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] <= t[2]);
			}

			public LogLE3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (domx.first() == 0 && domy.lastValue() <= domz.firstValue() && domx.remove(0) == false)
					return false;
				if (domx.last() == 1 && domy.firstValue() > domz.lastValue() && domx.remove(1) == false)
					return false;
				if (domx.first() != 0) { // only 1
					if (domy.removeValuesGreaterThan(domz.lastValue()) == false && domz.removeValuesLessThan(domy.firstValue()) == false)
						return false;
				}
				if (domx.last() != 1) { // only 0
					if (domy.removeValuesLessThanOrEqual(domz.firstValue()) == false && domz.removeValuesGreaterThanOrEqual(domy.lastValue()) == false)
						return false;
				}
				return true;
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
