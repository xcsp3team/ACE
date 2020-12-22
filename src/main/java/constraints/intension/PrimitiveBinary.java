/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.intension;

import java.math.BigInteger;

import org.xcsp.common.Types.TypeArithmeticOperator;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeUnaryArithmeticOperator;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.global.Sum.SumWeighted;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryDistb.DistbEQ2;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryMul.MulGE2;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryMul.MulLE2;
import constraints.intension.PrimitiveBinary.PropagatorEQ.MultiPropagatorEQ;
import constraints.intension.PrimitiveBinary.PropagatorEQ.SimplePropagatorEQ;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagSymmetric;
import interfaces.Tags.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

// Important: in Java, integer division rounds toward 0
// this implies that: 10/3 = 3, -10/3 = -3, 10/-3 = -3, -10/-3 = 3
// https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.17.2

public abstract class PrimitiveBinary extends Primitive implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	public static boolean enforceLT(Domain dx, Domain dy) { // x < y
		return dx.removeValuesGE(dy.lastValue()) && dy.removeValuesLE(dx.firstValue());
	}

	public static boolean enforceLT(Domain dx, Domain dy, int k) { // x < y + k
		return dx.removeValuesGE(dy.lastValue() + k) && dy.removeValuesLE(dx.firstValue() - k);
	}

	public static boolean enforceLE(Domain dx, Domain dy) { // x <= y
		return dx.removeValuesGT(dy.lastValue()) && dy.removeValuesLT(dx.firstValue());
	}

	public static boolean enforceLE(Domain dx, Domain dy, int k) { // x <= y + k
		return dx.removeValuesGT(dy.lastValue() + k) && dy.removeValuesLT(dx.firstValue() - k);
	}

	public static boolean enforceGE(Domain dx, Domain dy) { // x >= y
		return dx.removeValuesLT(dy.firstValue()) && dy.removeValuesGT(dx.lastValue());
	}

	public static boolean enforceGE(Domain dx, Domain dy, int k) { // x >= y + k
		return dx.removeValuesLT(dy.firstValue() + k) && dy.removeValuesGT(dx.lastValue() - k);
	}

	public static boolean enforceGT(Domain dx, Domain dy) { // x > y
		return dx.removeValuesLE(dy.firstValue()) && dy.removeValuesGE(dx.lastValue());
	}

	public static boolean enforceGT(Domain dx, Domain dy, int k) { // x > y + k
		return dx.removeValuesLE(dy.firstValue() + k) && dy.removeValuesGE(dx.lastValue() - k);
	}

	public static boolean enforceEQ(Domain dx, Domain dy) { // x = y
		if (dx.removeValuesNotIn(dy) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesNotIn(dx);
		assert consistent;
		return true;
	}

	// public static boolean enforceEQ(Domain dx, Domain dy, int k) { // x = y + k
	// if (dx.removeValuesAddNotIn(dy, -k) == false)
	// return false;
	// if (dx.size() == dy.size())
	// return true;
	// assert dx.size() < dy.size();
	// boolean consistent = dy.removeValuesAddNotIn(dx, k);
	// assert consistent;
	// return true;
	// }

	// public static boolean enforceMulEQ(Domain dx, Domain dy, int k) { // x = y * k
	// assert dx.iterateOnValuesStoppingWhen(v -> v != 0 && v % k != 0) == false; // we assume that trivial inconsistent values have been deleted
	// // initially (for code efficiency, avoiding systematic check)
	// if (dx.removeValuesDivNotIn(dy, k) == false)
	// return false;
	// if (dx.size() == dy.size())
	// return true;
	// assert dx.size() < dy.size();
	// boolean consistent = dy.removeValuesMulNotIn(dx, k);
	// assert consistent;
	// return true;
	// }

	public static boolean enforceNE(Domain dx, Domain dy) { // x != y
		if (dx.size() == 1)
			return dy.removeValueIfPresent(dx.uniqueValue());
		if (dy.size() == 1)
			return dx.removeValueIfPresent(dy.uniqueValue());
		return true;
	}

	// public static boolean enforceNE(Domain dx, Domain dy, int k) { // x != y + k
	// if (dx.size() == 1)
	// return dy.removeValueIfPresent(dx.uniqueValue() - k);
	// if (dy.size() == 1)
	// return dx.removeValueIfPresent(dy.uniqueValue() + k);
	// return true;
	// }

	public static boolean enforceAddLE(Domain dx, Domain dy, int k) { // x + y <= k
		return dx.removeValuesGT(k - dy.firstValue()) && dy.removeValuesGT(k - dx.firstValue());
	}

	public static boolean enforceAddGE(Domain dx, Domain dy, int k) { // x + y >= k
		return dx.removeValuesLT(k - dy.lastValue()) && dy.removeValuesLT(k - dx.lastValue());
	}

	public static boolean enforceMulLE(Domain dx, Domain dy, int k) { // x * y <= k
		return MulLE2.revise(dx, dy, k) && MulLE2.revise(dy, dx, k);
	}

	public static boolean enforceMulGE(Domain dx, Domain dy, int k) { // x * y >= k
		return MulGE2.revise(dx, dy, k) && MulGE2.revise(dy, dx, k);
	}

	public static boolean enforceDivLE(Domain dx, Domain dy, int k) { // x / y <= k
		return dx.removeValuesNumeratorsGT(k, dy.lastValue()) && dy.removeValuesDenominatorsGT(k, dx.firstValue());
	}

	public static boolean enforceDivGE(Domain dx, Domain dy, int k) { // x / y >= k
		return dx.removeValuesNumeratorsLT(k, dy.firstValue()) && dy.removeValuesDenominatorsLT(k, dx.lastValue());
	}

	public final static int UNITIALIZED = -1;

	public abstract static class PropagatorEQ {

		protected Domain dx, dy;

		protected int time;

		protected int[] times;

		protected boolean twoway;

		protected PropagatorEQ(Domain dx, Domain dy, boolean twoway) {
			this.dx = dx;
			this.dy = dy;
			this.times = new int[twoway ? Math.max(dx.initSize(), dy.initSize()) : dx.initSize()];
		}

		protected PropagatorEQ(Domain dx, Domain dy) {
			this(dx, dy, false);
		}

		protected abstract int nSupportsForWhenIteratingOver(Domain d1, Domain d2);

		public boolean runPropagator(Variable evt, Domain d1, Domain d2) {
			int sizeBefore = d2.size();
			int nSupports = nSupportsForWhenIteratingOver(d1, d2);
			if (nSupports == 0)
				return evt.dom.fail();
			d2.afterElementaryCalls(sizeBefore); // consistency is, from now on, ensured
			int toremove = d1.size() - nSupports;
			if (toremove == 0)
				return true;
			sizeBefore = d1.size();
			for (int a = d1.first(); a != -1 && toremove > 0; a = d1.next(a))
				if (times[a] != time) {
					d1.removeElementary(a);
					toremove--;
				}
			d1.afterElementaryCalls(sizeBefore);
			return true;
		}

		public boolean runPropagator(Variable evt) {
			time++;
			if (twoway && dx.size() < dy.size())
				return runPropagator(evt, dy, dx);
			return runPropagator(evt, dx, dy);
		}

		public abstract static class SimplePropagatorEQ extends PropagatorEQ {

			protected SimplePropagatorEQ(Domain dx, Domain dy, boolean twoway) {
				super(dx, dy, twoway);
			}

			abstract int valxFor(int b);

			int valyFor(int a) {
				throw new AssertionError("Missing implementation");
			}

			protected int nSupportsForWhenIteratingOver(Domain d1, Domain d2) {
				if (d2.size() == 1 && !d1.presentValue(d1 == dx ? valxFor(d2.unique()) : valyFor(d2.unique())))
					return 0;
				int cnt = 0;
				for (int b = d2.first(); b != -1; b = d2.next(b)) {
					int a = d1.toPresentIdx(d1 == dx ? valxFor(b) : valyFor(b));
					if (a == -1)
						d2.removeElementary(b);
					else if (times[a] != time) {
						times[a] = time;
						cnt++;
					}
				}
				return cnt;
			}
		}

		public abstract static class MultiPropagatorEQ extends PropagatorEQ {

			protected MultiPropagatorEQ(Domain dx, Domain dy, boolean twoway) {
				super(dx, dy, twoway);
			}

			abstract int[] valsxFor(int b);

			int[] valsyFor(int a) {
				throw new AssertionError("Missing implementation");
			}

			protected int nSupportsForWhenIteratingOver(Domain d1, Domain d2) {
				int cnt = 0;
				for (int b = d2.first(); b != -1; b = d2.next(b)) {
					boolean found = false;
					for (int va : d1 == dx ? valsxFor(b) : valsyFor(b)) {
						int a = d1.toPresentIdx(va);
						if (a != -1) {
							found = true;
							if (times[a] != time) {
								times[a] = time;
								cnt++;
							}
						}
					}
					if (!found) {
						if (d2.var().assigned())
							return 0;
						d2.removeElementary(b);
					}
				}
				return cnt;
			}
		}
	}

	// ************************************************************************
	// ***** Root class and Disjonctive
	// ************************************************************************

	protected final Variable x, y;

	protected final Domain dx, dy; // domains of x and y

	protected int[] rx, ry; // residues for x and y

	protected void buildResiduesForFirstVariable() {
		this.rx = Kit.repeat(UNITIALIZED, dx.initSize());
	}

	protected void buildResiduesForBothVariables() {
		this.rx = Kit.repeat(UNITIALIZED, dx.initSize());
		this.ry = Kit.repeat(UNITIALIZED, dy.initSize());
	}

	public PrimitiveBinary(Problem pb, Variable x, Variable y) {
		super(pb, pb.api.vars(x, y));
		this.x = x;
		this.y = y;
		this.dx = x.dom;
		this.dy = y.dom;
	}

	// ************************************************************************
	// *****Classes when no constant is involved
	// ************************************************************************

	public static final class Disjonctive extends PrimitiveBinary {

		final int kx, ky;

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
			return dx.removeValuesInRange(dy.lastValue() - kx + 1, dy.firstValue() + ky)
					&& dy.removeValuesInRange(dx.lastValue() - ky + 1, dx.firstValue() + kx);
		}
	}

	public static abstract class PrimitiveBinaryEQWithUnaryOperator extends PrimitiveBinary implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, TypeUnaryArithmeticOperator aop, Variable y) {
			switch (aop) {
			case ABS:
				return new DistbEQ2(pb, x, y, 0);
			case NEG:
				return new NegEQ2(pb, x, y);
			case SQR:
				return null;
			default: // NOT
				return null;
			}
		}

		public PrimitiveBinaryEQWithUnaryOperator(Problem pb, Variable x, Variable y) {
			super(pb, x, y);
		}

		public static final class NegEQ2 extends PrimitiveBinaryEQWithUnaryOperator {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] == -t[1];
			}

			private final SimplePropagatorEQ sp;

			public NegEQ2(Problem pb, Variable x, Variable y) {
				super(pb, x, y);
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					final int valxFor(int b) {
						return -dy.toVal(b);
					}

					final int valyFor(int a) {
						return -dx.toVal(a);
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy);
			}
		}
	}

	// ************************************************************************
	// ***** Root class when a constant k is involved
	// ************************************************************************

	public static abstract class PrimitiveBinaryWithCst extends PrimitiveBinary {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, TypeArithmeticOperator aop, Variable y, TypeConditionOperatorRel op, int k) {
			switch (aop) {
			case ADD:
				return PrimitiveBinaryAdd.buildFrom(pb, x, y, op, k);
			case SUB:
				return PrimitiveBinarySub.buildFrom(pb, x, y, op, k);
			case MUL:
				return PrimitiveBinaryMul.buildFrom(pb, x, y, op, k);
			case DIV:
				return PrimitiveBinaryDiv.buildFrom(pb, x, y, op, k);
			case MOD:
				return PrimitiveBinaryMod.buildFrom(pb, x, y, op, k);
			case DIST:
				return PrimitiveBinaryDist.buildFrom(pb, x, y, op, k);
			default:
				return null;
			}
		}

		public static Constraint buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, TypeArithmeticOperator aop, int k) {
			switch (aop) {
			case ADD:
				return PrimitiveBinarySub.buildFrom(pb, x, y, op, k);
			case SUB:
				return PrimitiveBinarySub.buildFrom(pb, x, y, op, -k);
			case MUL:
				return PrimitiveBinaryMulb.buildFrom(pb, x, op, y, k);
			case DIV:
				return PrimitiveBinaryDivb.buildFrom(pb, x, op, y, k);
			case MOD:
				return PrimitiveBinaryModb.buildFrom(pb, x, op, y, k);
			case DIST:
				return PrimitiveBinaryDistb.buildFrom(pb, x, op, y, k);
			default:
				return null;
			}
		}

		protected final int k;

		public PrimitiveBinaryWithCst(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
		}
	}

	// ************************************************************************
	// ***** Classes for x + y <op> k (CtrPrimitiveBinaryAdd)
	// ************************************************************************

	public static abstract class PrimitiveBinaryAdd extends PrimitiveBinaryWithCst implements TagSymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new AddLE2(pb, x, y, k - 1);
			case LE:
				return new AddLE2(pb, x, y, k);
			case GE:
				return new AddGE2(pb, x, y, k);
			case GT:
				return new AddGE2(pb, x, y, k + 1);
			case EQ:
				return new AddEQ2(pb, x, y, k); // return pb.extension(eq(add(x, y), k));
			case NE:
				return new AddNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryAdd(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		public static final class AddLE2 extends PrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] <= k;
			}

			public AddLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceAddLE(dx, dy, k); // dx.removeValuesGT(k - dy.firstValue()) && dy.removeValuesGT(k - dx.firstValue());
			}
		}

		public static final class AddGE2 extends PrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] >= k;
			}

			public AddGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceAddGE(dx, dy, k); // dx.removeValuesLT(k - dy.lastValue()) && dy.removeValuesLT(k - dx.lastValue());
			}
		}

		public static final class AddEQ2 extends PrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == k;
			}

			private final SimplePropagatorEQ sp;

			public AddEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					final int valxFor(int b) {
						return k - dy.toVal(b);
					}

					final int valyFor(int a) {
						return k - dx.toVal(a);
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy); // return dx.removeValuesSubNotIn_reverse(dy, k) && dy.removeValuesSubNotIn_reverse(dx, k);
			}
		}

		public static final class AddNE2 extends PrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] != k;
			}

			public AddNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return dy.removeValueIfPresent(k - dx.uniqueValue());
				if (dy.size() == 1)
					return dx.removeValueIfPresent(k - dy.uniqueValue());
				return true;
			}
		}
	}
	// ************************************************************************
	// ***** Classes for x - y <op> k (CtrPrimitiveBinarySub)
	// ************************************************************************

	public static abstract class PrimitiveBinarySub extends PrimitiveBinaryWithCst {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeOperatorRel op, int k) {
			return buildFrom(pb, x, y, op.toConditionOperator(), k);
		}

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new SubLE2(pb, x, y, k - 1);
			case LE:
				return new SubLE2(pb, x, y, k);
			case GE:
				return new SubGE2(pb, x, y, k);
			case GT:
				return new SubGE2(pb, x, y, k + 1);
			case EQ:
				return new SubEQ2(pb, x, y, k); // return pb.extension(pb.api.eq(pb.api.sub(x, y), k));
			case NE:
				return new SubNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinarySub(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		public static final class SubLE2 extends PrimitiveBinarySub implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] <= k;
			}

			public SubLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceLE(dx, dy, k);
			}
		}

		public static final class SubGE2 extends PrimitiveBinarySub implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] >= k;
			}

			public SubGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceGE(dx, dy, k);
			}
		}

		public static final class SubEQ2 extends PrimitiveBinarySub {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] - t[1] == k;
			}

			@Override
			public Boolean isSymmetric() {
				return k == 0;
			}

			private final SimplePropagatorEQ sp;

			public SubEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					final int valxFor(int b) {
						return k + dy.toVal(b);
					}

					final int valyFor(int a) {
						return dx.toVal(a) - k;
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy);
				// return enforceEQ(dx, dy, k);
			}
		}

		public static final class SubNE2 extends PrimitiveBinarySub {

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
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return dy.removeValueIfPresent(dx.uniqueValue() - k);
				if (dy.size() == 1)
					return dx.removeValueIfPresent(dy.uniqueValue() + k);
				return true;
				// return enforceNE(dx, dy, k);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> k (CtrPrimitiveBinaryMul)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMul extends PrimitiveBinaryWithCst implements TagSymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new MulLE2(pb, x, y, k - 1);
			case LE:
				return new MulLE2(pb, x, y, k);
			case GE:
				return new MulGE2(pb, x, y, k);
			case GT:
				return new MulGE2(pb, x, y, k + 1);
			case EQ:
				return new MulEQ2(pb, x, y, k);
			case NE:
				return new MulNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryMul(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
		}

		public static final class MulLE2Old extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] <= k;
			}

			public MulLE2Old(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			private boolean checkLimit(int c, int k, Domain dom) { // c*y <= k
				if (c == 0)
					return k >= 0;
				int limit = Kit.greatestIntegerLE(c, k);
				return c > 0 ? dom.firstValue() <= limit : dom.lastValue() >= limit;
			}

			private boolean revise(Domain d1, Domain d2) {
				int sizeBefore = d1.size();
				for (int a = d1.last(); a != -1; a = d1.prev(a)) {
					int va = d1.toVal(a);
					if ((va > 0 && d2.firstValue() >= 0 && va * d2.firstValue() <= k) || (va < 0 && d2.lastValue() >= 0 && va * d2.lastValue() <= k))
						break; // because all values of d1 are necessarily supported
					if (checkLimit(va, k, d2))
						continue;
					d1.removeElementary(a);
				}
				return d1.afterElementaryCalls(sizeBefore);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy) && revise(dy, dx);
			}
		}

		public static final class MulGE2Old extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] >= k;
			}

			public MulGE2Old(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			private boolean checkLimit(int c, int k, Domain dom) { // c*y >= k
				if (c == 0)
					return k <= 0;
				int limit = Kit.smallestIntegerGE(c, k);
				return c > 0 ? dom.lastValue() >= limit : dom.firstValue() <= limit;
			}

			private boolean revise(Domain d1, Domain d2) {
				int sizeBefore = d1.size();
				for (int a = d1.first(); a != -1; a = d1.next(a)) {
					int va = d1.toVal(a);
					if ((va > 0 && d2.lastValue() >= 0 && va * d2.lastValue() >= k) || (va < 0 && d2.firstValue() >= 0 && va * d2.firstValue() >= k))
						break; // because all values of d1 are necessarily supported
					if (checkLimit(va, k, d2))
						continue;
					d1.removeElementary(a);
				}
				return d1.afterElementaryCalls(sizeBefore);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy) && revise(dy, dx);
			}
		}

		public static final class MulLE2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] <= k;
			}

			public MulLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			public static boolean revise(Domain d1, Domain d2, int k) {
				if (d2.presentValue(0)) {
					if (0 <= k)
						return true;
					if (d2.removeValue(0) == false)
						return false;
				}
				assert !d2.presentValue(0);
				if (d2.firstValue() > 0) // all values in d2 are positive
					return d1.removeValuesGT(k > 0 ? Kit.greatestIntegerLE(d2.firstValue(), k) : Kit.greatestIntegerLE(d2.lastValue(), k));
				if (d2.lastValue() < 0) // all values in d2 are negative
					return d1.removeValuesLT(k < 0 ? Kit.smallestIntegerGE(-d2.firstValue(), -k) : Kit.smallestIntegerGE(-d2.lastValue(), -k));
				return d1.removeValuesInRange(Kit.greatestIntegerLE(d2.lastValue(), k) + 1, Kit.smallestIntegerGE(-d2.firstValue(), -k));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy, k) && revise(dy, dx, k);
			}
		}

		public static final class MulGE2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] >= k;
			}

			public MulGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			public static boolean revise(Domain d1, Domain d2, int k) {
				if (d2.presentValue(0)) {
					if (0 >= k)
						return true;
					if (d2.removeValue(0) == false)
						return false;
				}
				assert !d2.presentValue(0);
				if (d2.firstValue() > 0) // all values in d2 are positive
					return d1.removeValuesLT(k < 0 ? Kit.smallestIntegerGE(d2.firstValue(), k) : Kit.smallestIntegerGE(d2.lastValue(), k));
				if (d2.lastValue() < 0) // all values in d2 are negative
					return d1.removeValuesGT(k > 0 ? Kit.greatestIntegerLE(-d2.firstValue(), -k) : Kit.greatestIntegerLE(-d2.lastValue(), -k));
				return d1.removeValuesInRange(Kit.greatestIntegerLE(-d2.firstValue(), -k) + 1, Kit.smallestIntegerGE(d2.lastValue(), k));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy, k) && revise(dy, dx, k);
			}
		}

		public static final class MulEQ2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] == k;
			}

			private final SimplePropagatorEQ sp;

			public MulEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k > 1, "if k is 0 or 1, other constraints should be posted"); // TODO could we just impose k != 0?
				dx.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
				dy.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					final int valxFor(int b) {
						return k / dy.toVal(b);
					}

					final int valyFor(int a) {
						return k / dx.toVal(a);
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy); // return dx.removeValuesInvNotIn(dy, k) && dy.removeValuesInvNotIn(dx, k);
			}
		}

		public static final class MulNE2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] != k;
			}

			public MulNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k > 1, "if k is 0 or 1, other constraints should be posted");
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1) {
					int va = dx.uniqueValue();
					if (va != 0 && k % va == 0)
						return dy.removeValueIfPresent(k / va);
				} else if (dy.size() == 1) {
					int vb = dy.uniqueValue();
					if (vb != 0 && k % vb == 0)
						return dx.removeValueIfPresent(k / vb);
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x / y <op> k (CtrPrimitiveBinaryDiv)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDiv extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new DivLE2(pb, x, y, k - 1);
			case LE:
				return new DivLE2(pb, x, y, k);
			case GE:
				return new DivGE2(pb, x, y, k);
			case GT:
				return new DivGE2(pb, x, y, k + 1);
			case EQ:
				return new DivEQ2(pb, x, y, k);
			case NE:
				return null;
			// return new DivNE2(pb, x, y, k)); // TODO
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryDiv(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
		}

		public static final class DivLE2 extends PrimitiveBinaryDiv {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] <= k;
			}

			public DivLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceDivLE(dx, dy, k); // dx.removeValuesNumeratorsGT(k, dy.lastValue()) && dy.removeValuesDenominatorsGT(k, dx.firstValue());
			}
		}

		public static final class DivGE2 extends PrimitiveBinaryDiv {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] >= k;
			}

			public DivGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceDivGE(dx, dy, k); // dx.removeValuesNumeratorsLT(k, dy.firstValue()) && dy.removeValuesDenominatorsLT(k, dx.lastValue());
			}
		}

		// Be careful: x/y = k is not equivalent to x/k = y (for example, 13/5 = 2 while 13/2 = 6)
		public static final class DivEQ2 extends PrimitiveBinaryDiv {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] == k;
			}

			public DivEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				buildResiduesForBothVariables();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if ((dx.lastValue() / dy.firstValue() < k) || (dx.firstValue() / dy.lastValue() > k)) // possible because only positive values
					return dx.fail();
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (rx[a] != UNITIALIZED && dy.present(rx[a]))
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int res = va / dy.toVal(b);
						if (res < k)
							break;
						if (res == k) {
							rx[a] = b;
							continue extern;
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (ry[b] != UNITIALIZED && dx.present(ry[b]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int res = dx.toVal(a) / vb;
						if (res > k)
							break;
						if (res == k) {
							ry[b] = a;
							continue extern;
						}
					}
					if (dy.remove(b) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x % y <op> k (CtrPrimitiveBinaryMod)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMod extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case EQ:
				return new ModEQ2(pb, x, y, k);
			default:
				return null;
			}
		}

		public PrimitiveBinaryMod(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
		}

		public static final class ModEQ2 extends PrimitiveBinaryMod {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] % t[1] == k;
			}

			public ModEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				buildResiduesForBothVariables();
				dx.removeValuesAtConstructionTime(v -> v < k); // because the remainder is at most k-1, whatever the value of y
				dy.removeValuesAtConstructionTime(v -> v <= k); // because the remainder is at most k-1, whatever the value for x
				// note that k for x is always supported, whatever the remaining value in y
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					if (rx[a] != UNITIALIZED && dy.present(rx[a]))
						continue;
					int va = dx.toVal(a);
					if (va == k)
						continue; // because dy.lastValue() > k by construction (see constructor), and so there is a support
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (va % vb == k) {
							rx[a] = b;
							continue extern;
						} else {
							if (va < vb) // means that the remainder with remaining values of y always lead to va (and it is not k)
								break;
							// here, we know that va >= vb and va != k (see code earlier)
							if (va < 2 * vb) { // it means that the quotient was 1, and will remain 1 (and 0 later)
								assert va / vb == 1;
								if (va - k <= vb || dy.presentValue(va - k) == false)
									break;
								rx[a] = dy.toVal(va - k);
								continue extern;
							}
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					if (ry[b] != UNITIALIZED && dx.present(ry[b]))
						continue;
					int vb = dy.toVal(b);
					int nMultiples = dx.lastValue() / vb;
					if (dx.size() <= nMultiples) {
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int va = dx.toVal(a);
							if (va % vb == k) {
								ry[b] = a;
								continue extern;
							}
						}
					} else {
						// we know that va >= k and vb > k by construction
						int va = vb + k; // no neex to start at va = k because k % vb is 0 (and 0 is not possible for k)
						while (va <= dx.lastValue()) {
							assert va % vb == k;
							if (dx.presentValue(va)) {
								ry[b] = dx.toIdx(va);
								continue extern;
							}
							va += vb;
						}
					}
					if (dy.remove(b) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for |x - y| <op> k (CtrPrimitiveBinaryDist)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDist extends PrimitiveBinaryWithCst implements TagSymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new DistLE2(pb, x, y, k - 1); // return pb.extension(lt(dist(x, y), k));
			case LE:
				return new DistLE2(pb, x, y, k); // return pb.extension(le(dist(x, y), k));
			case GE:
				return new DistGE2(pb, x, y, k);
			case GT:
				return new DistGE2(pb, x, y, k + 1);
			case EQ:
				return new DistEQ2(pb, x, y, k); // return pb.extension(eq(dist(x, y), k));
			// ok for java ac csp/Rlfap-scen-11-f06.xml.lzma -cm -ev -varh=Dom but not for domOnwdeg. Must be because of failing may occur on assigned
			// variables in DISTEQ2
			case NE:
				return new DistNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryDist(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(k > 0, "k should be strictly positive");
		}

		public static final class DistLE2 extends PrimitiveBinaryDist {

			@Override
			public boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) <= k;
			}

			public DistLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesAtDistanceGT(k, dy) && dy.removeValuesAtDistanceGT(k, dx);
			}
		}

		public static final class DistGE2 extends PrimitiveBinaryDist { // code similar to Disjunctive

			@Override
			public boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) >= k; // equivalent to disjunctive: t[0] + k <= t[1] || t[1] + k <= t[0];
			}

			public DistGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesInRange(dy.lastValue() - k + 1, dy.firstValue() + k)
						&& dy.removeValuesInRange(dx.lastValue() - k + 1, dx.firstValue() + k);
			}
		}

		public static final class DistEQ2 extends PrimitiveBinaryDist {

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) == k;
			}

			private final MultiPropagatorEQ sp;

			public DistEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				int[] tmp = new int[2];
				this.sp = new MultiPropagatorEQ(dx, dy, true) {
					final int[] valsxFor(int b) {
						tmp[0] = dy.toVal(b) + k;
						tmp[1] = dy.toVal(b) - k;
						return tmp;
					}

					final int[] valsyFor(int a) {
						tmp[0] = dx.toVal(a) + k;
						tmp[1] = dx.toVal(a) - k;
						return tmp;
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy); // return dx.removeValuesAtDistanceNE(k, dy) && dy.removeValuesAtDistanceNE(k, dx);
			}
		}

		public static final class DistNE2 extends PrimitiveBinaryDist {

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) != k;
			}

			public DistNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			private boolean revise(Domain d1, Domain d2) {
				if (d1.size() == 1)
					return d2.removeValuesIfPresent(d1.uniqueValue() - k, d1.uniqueValue() + k);
				if (d1.size() == 2 && d1.lastValue() - k == d1.firstValue() + k)
					return d2.removeValueIfPresent(d1.lastValue() - k);
				return true;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy) && revise(dy, dx);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x <op> y * k (CtrPrimitiveBinaryMulb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMulb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static Constraint buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
			switch (op) {
			case LT:
			case LE:
			case GE:
			case GT:
				return SumWeighted.buildFrom(pb, pb.api.vars(x, y), pb.api.vals(1, -k), op, 0);
			case EQ:
				return new MulbEQ2(pb, x, y, k);
			case NE:
				return new MulbNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryMulb(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(k != 0);
			control(Utilities.isSafeInt(BigInteger.valueOf(dy.firstValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
			control(Utilities.isSafeInt(BigInteger.valueOf(dy.lastValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
		}

		public static final class MulbEQ2 extends PrimitiveBinaryMulb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] == t[1] * k;
			}

			private final SimplePropagatorEQ sp;

			public MulbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				dx.removeValuesAtConstructionTime(v -> v != 0 && v % k != 0); // non multiple deleted (important for avoiding systematic checks)
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					final int valxFor(int b) {
						return dy.toVal(b) * k;
					}

					final int valyFor(int a) {
						return dx.toVal(a) / k;
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy); // return enforceMulEQ(dx, dy, k);
			}
		}

		public static final class MulbNE2 extends PrimitiveBinaryMulb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != t[1] * k;
			}

			public MulbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				// note that values in x that are not multiple of k are always supported
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return dx.uniqueValue() % k != 0 || dy.removeValueIfPresent(dx.uniqueValue() / k);
				if (dy.size() == 1)
					return dx.removeValueIfPresent(dy.uniqueValue() * k);
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x <op> y / k (CtrPrimitiveBinaryDivb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDivb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
			switch (op) {
			case EQ:
				return new DivbEQ2(pb, x, y, k);
			case NE:
				return new DivbNE2(pb, x, y, k);
			default:
				return null;
			}
		}

		public PrimitiveBinaryDivb(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() >= 0 && k > 1);
		}

		public static final class DivbEQ2 extends PrimitiveBinaryDivb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] == t[1] / k;
			}

			private final SimplePropagatorEQ sp;

			public DivbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.sp = new SimplePropagatorEQ(dx, dy, false) {
					final int valxFor(int b) {
						return dy.toVal(b) / k;
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy);
			}
		}

		public static final class DivbNE2 extends PrimitiveBinaryDivb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != t[1] / k;
			}

			public DivbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return dy.removeValuesInRange(dx.uniqueValue() * k, dx.uniqueValue() * k + k);
				if (dy.firstValue() / k == dy.lastValue() / k)
					return dx.removeValueIfPresent(dy.firstValue() / k);
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x <op> y % k (CtrPrimitiveBinaryModb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryModb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
			switch (op) {
			case EQ:
				return new ModbEQ2(pb, x, y, k);
			case NE:
				return new ModbNE2(pb, x, y, k);
			default:
				return null;
			}
		}

		public PrimitiveBinaryModb(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() >= 0 && k > 1);
		}

		public static final class ModbEQ2 extends PrimitiveBinaryModb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] == t[1] % k;
			}

			private final SimplePropagatorEQ sp;

			public ModbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				dx.removeValuesAtConstructionTime(v -> v >= k); // because the remainder is at most k-1, whatever the value of y
				this.sp = new SimplePropagatorEQ(dx, dy, false) {
					final int valxFor(int b) {
						return dy.toVal(b) % k;
					}
				};
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return sp.runPropagator(dummy);
			}
		}

		public static final class ModbNE2 extends PrimitiveBinaryModb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != t[1] % k;
			}

			public ModbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			int watch1 = -1, watch2 = -1; // watching two different (indexes of) values of y leading to two different remainders

			private int findWatch(int other) {
				if (other == -1)
					return dy.first();
				int r = dy.toVal(other) % k;
				for (int b = dy.first(); b != -1; b = dy.next(b))
					if (dy.toVal(b) % k != r)
						return b;
				return -1;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1) {
					entailed();
					return dy.removeValuesModIn(dx, k);
				}
				if (watch1 == -1 || !dy.present(watch1))
					watch1 = findWatch(watch2);
				if (watch1 == -1) {
					// watch2 is the only remaining valid watch (we know that it is still valid since the domain is not empty)
					assert watch2 != -1 && dy.present(watch2);
					entailed();
					return dx.removeValueIfPresent(dy.toVal(watch2) % k);
				}
				if (watch2 == -1 || !dy.present(watch2))
					watch2 = findWatch(watch1);
				if (watch2 == -1) {
					entailed();
					return dx.removeValueIfPresent(dy.toVal(watch1) % k);
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x <op> |y - k| (CtrPrimitiveBinaryDistb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDistb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
			switch (op) {
			case EQ:
				return new DistbEQ2(pb, x, y, k);
			case NE:
				return new DistbNE2(pb, x, y, k);
			default:
				return null;
			}
		}

		public PrimitiveBinaryDistb(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0);
			control(k >= 0, "k should be positive or 0");

		}

		public static final class DistbEQ2 extends PrimitiveBinaryDistb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] == Math.abs(t[1] - k);
			}

			private final SimplePropagatorEQ sp;

			public DistbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.sp = new SimplePropagatorEQ(dx, dy, false) {
					final int valxFor(int b) {
						return Math.abs(dy.toVal(b) - k);
					}
				};
			}

			@Override
			public boolean runPropagator(Variable evt) {
				if (dx.size() == 1 && !dy.presentValue(k + dx.uniqueValue()) && !dy.presentValue(k - dx.uniqueValue()))
					return evt.dom.fail();
				return sp.runPropagator(evt);
			}
		}

		public static final class DistbNE2 extends PrimitiveBinaryDistb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != Math.abs(t[1] - k);
			}

			public DistbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return dy.removeValuesIfPresent(k + dx.uniqueValue(), k - dx.uniqueValue());
				int v = Math.abs(dy.firstValue() - k);
				if (dy.size() == 1)
					return dx.removeValueIfPresent(v);
				if (dy.size() == 2 && Math.abs(dy.lastValue() - k) == v)
					return dx.removeValueIfPresent(v);
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x = (y <op> k) (CtrPrimitiveBinaryLog)
	// ************************************************************************

	public static abstract class PrimitiveBinaryLog extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static PrimitiveBinary buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return new LogLE2(pb, x, y, k - 1);
			case LE:
				return new LogLE2(pb, x, y, k);
			case GE:
				return new LogGE2(pb, x, y, k);
			case GT:
				return new LogGE2(pb, x, y, k + 1);
			case EQ:
				return new LogEQ2(pb, x, y, k);
			case NE:
				return new LogNE2(pb, x, y, k);
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryLog(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.is01(), "The first variable should be of type 01");
		}

		public static final class LogLE2 extends PrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] <= k);
			}

			public LogLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return dy.firstValue() > k || dy.removeValuesLE(k); // x = 0 => y > k
				if (dx.first() == 1)
					return dy.lastValue() <= k || dy.removeValuesGT(k); // x = 1 => y <= k
				if (dy.lastValue() <= k)
					return dx.removeIfPresent(0); // y <= k => x != 0
				if (dy.firstValue() > k)
					return dx.removeIfPresent(1); // y > k => x != 1
				return true;
			}
		}

		public static final class LogGE2 extends PrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] >= k);
			}

			public LogGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return dy.lastValue() < k || dy.removeValuesGE(k); // x = 0 => y < k
				if (dx.first() == 1)
					return dy.firstValue() >= k || dy.removeValuesLT(k); // x = 1 => y >= k
				if (dy.firstValue() >= k)
					return dx.removeIfPresent(0); // y >= k => x != 0
				if (dy.lastValue() < k)
					return dx.removeIfPresent(1); // y < k => x != 1
				return true;
			}
		}

		public static final class LogEQ2 extends PrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] == k);
			}

			public LogEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return dy.removeValueIfPresent(k); // x = 0 => y != k
				if (dx.first() == 1)
					return dy.reduceToValue(k); // x = 1 => y = k
				if (!dy.presentValue(k))
					return dx.removeIfPresent(1); // y != k => x != 1
				if (dy.size() == 1)
					return dx.removeIfPresent(0); // y = k => x != 0
				return true;
			}
		}

		public static final class LogNE2 extends PrimitiveBinaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] != k);
			}

			public LogNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0)
					return dy.reduceToValue(k); // x = 0 => y = k
				if (dx.first() == 1)
					return dy.removeValueIfPresent(k); // x = 1 => x != k
				if (!dy.presentValue(k))
					return dx.removeIfPresent(0); // y != k => x != 0
				if (dy.size() == 1)
					return dx.removeIfPresent(1); // y = k => x != 1
				return true;
			}
		}
	}
}
