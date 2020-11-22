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

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.global.SumWeighted;
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

	public static boolean enforceEQ(Domain dx, Domain dy, int k) { // x = y + k
		if (dx.removeValuesAddNotIn(dy, -k) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesAddNotIn(dx, k);
		assert consistent;
		return true;
	}

	public static boolean enforceMulEQ(Domain dx, Domain dy, int k) { // x = y * k
		assert dx.iterateOnValuesStoppingWhen(v -> v != 0 && v % k != 0) == false; // we assume that trivial inconsistent values have been deleted
		// initially (for code efficiency, avoiding systematic check)
		if (dx.removeValuesDivNotIn(dy, k) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesMulNotIn(dx, k);
		assert consistent;
		return true;
	}

	public static boolean enforceNE(Domain dx, Domain dy) { // x != y
		if (dx.size() == 1 && dy.removeValueIfPresent(dx.uniqueValue()) == false)
			return false;
		if (dy.size() == 1 && dx.removeValueIfPresent(dy.uniqueValue()) == false)
			return false;
		return true;
	}

	public static boolean enforceNE(Domain dx, Domain dy, int k) { // x != y + k
		if (dx.size() == 1 && dy.removeValueIfPresent(dx.uniqueValue() - k) == false)
			return false;
		if (dy.size() == 1 && dx.removeValueIfPresent(dy.uniqueValue() + k) == false)
			return false;
		return true;
	}

	public static boolean enforceMulNE(Domain dx, Domain dy, int k) { // x != y * k
		if (dx.size() == 1 && dx.uniqueValue() % k == 0 && dy.removeValueIfPresent(dx.uniqueValue() / k) == false)
			return false;
		if (dy.size() == 1 && dx.removeValueIfPresent(dy.uniqueValue() * k) == false)
			return false;
		return true;
	}

	public final static int UNITIALIZED = -1;

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

	// ************************************************************************
	// ***** Root class when a constant k is involved
	// ************************************************************************

	public static abstract class PrimitiveBinaryWithCst extends PrimitiveBinary {

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

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new AddLE2(pb, x, y, k - 1));
			case LE:
				return pb.addCtr(new AddLE2(pb, x, y, k));
			case GE:
				return pb.addCtr(new AddGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new AddGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new AddEQ2(pb, x, y, k)); // return pb.extension(eq(add(x, y), k));
			case NE:
				return pb.addCtr(new AddNE2(pb, x, y, k));
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
				return dx.removeValuesGT(k - dy.firstValue()) && dy.removeValuesGT(k - dx.firstValue());
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
				return dx.removeValuesLT(k - dy.lastValue()) && dy.removeValuesLT(k - dx.lastValue());
			}
		}

		public static final class AddEQ2 extends PrimitiveBinaryAdd {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == k;
			}

			public AddEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesSubNotIn_reverse(dy, k) && dy.removeValuesSubNotIn_reverse(dx, k);
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
			public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable x, int a) {
				return 1;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return (dx.size() > 1 || dy.removeValueIfPresent(k - dx.uniqueValue())) && (dy.size() > 1 || dx.removeValueIfPresent(k - dy.uniqueValue()));
			}
		}
	}
	// ************************************************************************
	// ***** Classes for x - y <op> k (CtrPrimitiveBinarySub)
	// ************************************************************************

	public static abstract class PrimitiveBinarySub extends PrimitiveBinaryWithCst {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new SubLE2(pb, x, y, k - 1));
			case LE:
				return pb.addCtr(new SubLE2(pb, x, y, k));
			case GE:
				return pb.addCtr(new SubGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new SubGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new SubEQ2(pb, x, y, k)); //
			// return pb.extension(pb.api.eq(pb.api.sub(x, y), k));
			case NE:
				return pb.addCtr(new SubNE2(pb, x, y, k));
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

			public SubEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public Boolean isSymmetric() {
				return k == 0;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceEQ(dx, dy, k);
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
			public int giveUpperBoundOfMaxNumberOfConflictsFor(Variable x, int a) {
				return 1;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceNE(dx, dy, k);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> k (CtrPrimitiveBinaryMul)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMul extends PrimitiveBinaryWithCst implements TagSymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new MulLE2(pb, x, y, k - 1));
			case LE:
				return pb.addCtr(new MulLE2(pb, x, y, k));
			case GE:
				return pb.addCtr(new MulGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new MulGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new MulEQ2(pb, x, y, k));
			case NE:
				return pb.addCtr(new MulNE2(pb, x, y, k));
			}
			throw new AssertionError();
		}

		public PrimitiveBinaryMul(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
		}

		public static final class MulLE2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] <= k;
			}

			public MulLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			// (3,-5) => -2; (3,10) => 3; (-3,-5) => 2; (-3,10) => -3; (3,0) => 0; (-3,0) => 0
			// 3y <= -5 => y <= -2; 3y <= 10 => y <= 3; -3y <= -5 => y >= 2; -3y <= 10 => y >= -3; 3y <= 0 => y <= 0; -3y <= 0 => y >= 0
			private boolean checkLimit(int c, int k, Domain dom) { // c*y <= k
				if (c == 0)
					return k >= 0;
				int limit = k / c;
				if (k < 0 && k % c != 0)
					limit += (limit < 0 ? -1 : 1);
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

		public static final class MulGE2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] >= k;
			}

			public MulGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			// (3,-5) => -1; (3,10) => 4; (-3,-5) => 1; (-3,10) => -4; (3,0) => 0; (-3,0) => 0
			// 3y >= -5 => y >= -1; 3y >= 10 => y >= 4; -3y >= -5 => y <= 1; -3y >= 10 => y <= -4; 3y >= 0 => y>= 0; -3y >= 0 => y <= 0
			public static boolean checkLimit(int c, int k, Domain dom) { // c*y >= k
				if (c == 0)
					return k <= 0;
				int limit = k / c;
				if (k > 0 && k % c != 0)
					limit += (limit < 0 ? -1 : 1);
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

		public static final class MulEQ2 extends PrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] == k;
			}

			public MulEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k > 1, "if k is 0 or 1, other constraints should be posted");
				dx.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
				dy.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesInvNotIn(dy, k) && dy.removeValuesInvNotIn(dx, k);
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
					if (va != 0 && k % va == 0 && dy.removeValueIfPresent(k / va) == false)
						return false;
				}
				if (dy.size() == 1) {
					int vb = dy.uniqueValue();
					if (vb != 0 && k % vb == 0 && dx.removeValueIfPresent(k / vb) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x <op> k * y (CtrPrimitiveBinaryMulb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMulb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, int k, Variable y) {
			switch (op) {
			case LT:
			case LE:
			case GE:
			case GT:
				return pb.addCtr(SumWeighted.buildFrom(pb, pb.api.vars(x, y), pb.api.vals(1, -k), op, 0));
			case EQ:
				return pb.addCtr(new MulbEQ2(pb, x, y, k));
			case NE:
				return pb.addCtr(new MulbNE2(pb, x, y, k));
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
				return t[0] == k * t[1];
			}

			public MulbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				dx.removeValuesAtConstructionTime(v -> v != 0 && v % k != 0); // non multiple deleted (important for avoiding systematic checks)
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceMulEQ(dx, dy, k);
			}
		}

		public static final class MulbNE2 extends PrimitiveBinaryMulb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != k * t[1];
			}

			public MulbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				// note that values in x that are not multiple of k are always supported
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceMulNE(dx, dy, k);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x / y <op> k (CtrPrimitiveBinaryDiv)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDiv extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new DivLE2(pb, x, y, k - 1));
			case LE:
				return pb.addCtr(new DivLE2(pb, x, y, k));
			case GE:
				return pb.addCtr(new DivGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new DivGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new DivEQ2(pb, x, y, k));
			// case NE:
			// return pb.addCtr(new DivNE2(pb, x, y, k)); // TODO
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
				return dx.removeValuesNumeratorsGT(k, dy.lastValue()) && dy.removeValuesDenominatorsGT(k, dx.firstValue());
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
				return dx.removeValuesNumeratorsLT(k, dy.firstValue()) && dy.removeValuesDenominatorsLT(k, dx.lastValue());
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
					if (rx[a] != UNITIALIZED && dy.isPresent(rx[a]))
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
					if (ry[b] != UNITIALIZED && dx.isPresent(ry[b]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(b)) {
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
	// ***** Classes for x <op> y / k (CtrPrimitiveBinaryDivb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDivb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			// case LT:
			// return pb.addCtr(new DivbLE2(pb, x, y, k - 1)); // TODO
			// case LE:
			// return pb.addCtr(new DivbLE2(pb, x, y, k));
			// case GE:
			// return pb.addCtr(new DivbGE2(pb, x, y, k));
			// case GT:
			// return pb.addCtr(new DivbGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new DivbEQ2(pb, x, y, k));
			case NE:
				return pb.addCtr(new DivbNE2(pb, x, y, k));
			}
			throw new AssertionError();
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

			public DivbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				buildResiduesForFirstVariable();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				int sizeBefore = dx.size();
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					if (rx[a] != UNITIALIZED && dy.isPresent(rx[a]))
						continue;
					int va = dx.toVal(a);
					if (dy.size() < k) {
						for (int b = dy.first(); b != -1; b = dy.next(b))
							if (va == dy.toVal(b) / k) {
								rx[a] = b;
								continue extern;
							}
					} else {
						int base = va * k;
						for (int i = 0; i < k; i++)
							if (dy.isPresentValue(base + i)) {
								rx[a] = dy.toIdx(base + i);
								continue extern;
							}
					}
					dx.removeElementary(a);
				}
				if (dx.afterElementaryCalls(sizeBefore) == false)
					return false;
				return dy.removeValuesDivNotIn(dx, k);
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
				if (dx.size() == 1 && dy.removeValuesInRange(dx.uniqueValue() * k, dx.uniqueValue() * k + k) == false)
					return false;
				if (dy.firstValue() / k == dy.lastValue() / k && dx.removeValueIfPresent(dy.firstValue() / k) == false)
					return false;
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x % y <op> k (CtrPrimitiveBinaryMod)
	// ************************************************************************

	public static abstract class PrimitiveBinaryMod extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new ModEQ2(pb, x, y, k));
			throw new AssertionError();
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
					if (rx[a] != UNITIALIZED && dy.isPresent(rx[a]))
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
								if (va - k <= vb || dy.isPresentValue(va - k) == false)
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
					if (ry[b] != UNITIALIZED && dx.isPresent(ry[b]))
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
							if (dx.isPresentValue(va)) {
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
	// ***** Classes for x <op> y % k (CtrPrimitiveBinaryModb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryModb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new ModbEQ2(pb, x, y, k));
			if (op == TypeConditionOperatorRel.NE)
				return pb.addCtr(new ModbNE2(pb, x, y, k));
			throw new AssertionError();
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

			public ModbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				buildResiduesForFirstVariable();
				dx.removeValuesAtConstructionTime(v -> v >= k); // because the remainder is at most k-1, whatever the value of y
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (rx[a] != UNITIALIZED && dy.isPresent(rx[a]))
						continue;
					int nMultiples = dy.lastValue() / k;
					if (dy.size() <= nMultiples) {
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vb = dy.toVal(b);
							if (vb % k == va) {
								rx[a] = b;
								continue extern;
							}
						}
					} else {
						int vb = va;
						while (vb <= dy.lastValue()) {
							assert vb % k == va;
							if (dy.isPresentValue(vb)) {
								rx[a] = dy.toIdx(vb);
								continue extern;
							}
							vb += k;
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				return dy.removeValuesModNotIn(dx, k);
			}
		}

		public static final class ModbNE2 extends PrimitiveBinaryModb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] != t[1] % k;
			}

			int watch1 = -1, watch2 = -1;

			private int findWatch(int other) {
				for (int b = dy.first(); b != -1; b = dy.next(b))
					if (dy.toVal(b) % k != other)
						return b;
				return -1;
			}

			public ModbNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				// we should record entailment to avoid making systematically O(d) when the constraitn is entailed

				if (dx.size() == 1)
					return dy.removeValuesModIn(dx, k);
				if (watch1 == -1 || !dy.isPresent(watch1))
					watch1 = findWatch(watch2);
				if (watch1 == -1) {
					// watch2 is the only remaining valid watch (we know that it is still valid)
					assert watch2 != -1 && dy.isPresent(watch2);
					if (dx.removeValueIfPresent(dy.toVal(watch2) % k) == false)
						return false;
				} else {
					if (watch2 == -1 || !dy.isPresent(watch2))
						watch2 = findWatch(watch1);
					if (watch2 == -1)
						if (dx.removeValueIfPresent(dy.toVal(watch1) % k) == false)
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

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new DistLE2(pb, x, y, k - 1)); // return pb.extension(lt(dist(x, y), k));
			case LE:
				return pb.addCtr(new DistLE2(pb, x, y, k)); // return pb.extension(le(dist(x, y), k));
			case GE:
				return pb.addCtr(new DistGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new DistGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new DistEQ2(pb, x, y, k)); // return pb.extension(eq(dist(x, y), k));
			// ok for java ac csp/Rlfap-scen-11-f06.xml.lzma -cm -ev -varh=Dom but not for domOnwdeg. Must be because of failing may occur on assigned
			// variables in DISTEQ2
			case NE:
				return pb.addCtr(new DistNE2(pb, x, y, k));
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

			public DistEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesAtDistanceNE(k, dy) && dy.removeValuesAtDistanceNE(k, dx);
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
	// ***** Classes for x <op> |y - k| (CtrPrimitiveBinaryDistb)
	// ************************************************************************

	public static abstract class PrimitiveBinaryDistb extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
			switch (op) {
			case EQ:
				return pb.addCtr(new DistbEQ2(pb, x, y, k));
			case NE:
				return pb.addCtr(new DistbNE2(pb, x, y, k));
			}
			throw new AssertionError();
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

			public DistbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (k == 0)
					return dx.removeValuesAbsNotIn_reverse(dy) && dy.removeValuesAbsNotIn(dx);
				else
					return dx.removeValuesDistNotIn_reverse(dy, k) && dy.removeValuesDistNotIn(dx, k);
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
				if (dx.size() == 1 && dy.removeValuesIfPresent(k + dx.uniqueValue(), k - dx.uniqueValue()) == false)
					return false;
				if (dy.size() == 1 && dx.removeValueIfPresent(Math.abs(dy.uniqueValue() - k)) == false)
					return false;
				if (dy.size() == 2 && Math.abs(dy.lastValue() - k) == Math.abs(dy.firstValue() - k)
						&& dx.removeValueIfPresent(Math.abs(dy.lastValue() - k)) == false)
					return false;
				return true;
			}
		}

	}

	// ************************************************************************
	// ***** Classes for x = (y <op> k) (CtrPrimitiveBinaryLog)
	// ************************************************************************

	public static abstract class PrimitiveBinaryLog extends PrimitiveBinaryWithCst implements TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			switch (op) {
			case LT:
				return pb.addCtr(new LogLE2(pb, x, y, k - 1));
			case LE:
				return pb.addCtr(new LogLE2(pb, x, y, k));
			case GE:
				return pb.addCtr(new LogGE2(pb, x, y, k));
			case GT:
				return pb.addCtr(new LogGE2(pb, x, y, k + 1));
			case EQ:
				return pb.addCtr(new LogEQ2(pb, x, y, k));
			case NE:
				return pb.addCtr(new LogNE2(pb, x, y, k));
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
				if (dx.first() == 0 && dy.lastValue() <= k && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.firstValue() > k && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && dy.lastValue() > k && dy.removeValuesGT(k) == false)
					return false;
				if (dx.last() == 0 && dy.firstValue() <= k && dy.removeValuesLE(k) == false)
					return false;
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
				if (dx.first() == 0 && dy.firstValue() >= k && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.lastValue() < k && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && dy.firstValue() < k && dy.removeValuesLT(k) == false)
					return false;
				if (dx.last() == 0 && dy.lastValue() >= k && dy.removeValuesGE(k) == false)
					return false;
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
				if (!dy.isPresentValue(k)) {
					if (dx.removeIfPresent(1) == false)
						return false;
				} else if (dy.size() == 1) {
					if (dx.removeIfPresent(0) == false)
						return false;
				}
				if (dx.size() == 1) {
					if (dx.first() == 0 && dy.removeValueIfPresent(k) == false)
						return false;
					if (dx.first() == 1 && dy.reduceToValue(k) == false)
						return false;
				}
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
				if (!dy.isPresentValue(k)) {
					if (dx.removeIfPresent(0) == false)
						return false;
				} else if (dy.size() == 1) {
					if (dx.removeIfPresent(1) == false)
						return false;
				}
				if (dx.size() == 1) {
					if (dx.first() == 0 && dy.reduceToValue(k) == false)
						return false;
					if (dx.first() == 1 && dy.removeValueIfPresent(k) == false)
						return false;
				}
				return true;
			}
		}

	}
}

// int cc = c >= 0 ? c : -c;
// int kk = k >= 0 ? k : -k;
// int limit = (kk / cc + (k < 0 && kk % cc != 0 ? 1 : 0)) * ((c < 0) != (k < 0) ? -1 : 1);
// System.out.println("limit1 " + limit + " " + (-5) % (-5));

// if (dx.size() == 1 && dy.removeValuesIfPresent(dx.uniqueValue(), -dx.uniqueValue()) == false)
// return false;
// if (dy.size() == 1 && dx.removeValueIfPresent(Math.abs(dy.uniqueValue())) == false)
// return false;
// if (dy.size() == 2 && dy.lastValue() == -dy.firstValue() && dx.removeValueIfPresent(dy.lastValue()) == false)
// return false;