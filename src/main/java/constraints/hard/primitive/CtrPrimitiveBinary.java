/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import java.math.BigInteger;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.hard.global.SumWeighted;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagSymmetric;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import utility.exceptions.UnreachableCodeException;
import variables.Variable;
import variables.domains.Domain;

// Important: in Java, integer division rounds toward 0
// this implies that: 10/3 = 3, -10/3 = -3, 10/-3 = -3, -10/-3 = 3
// https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.17.2

public abstract class CtrPrimitiveBinary extends CtrPrimitive implements TagGACGuaranteed, TagFilteringCompleteAtEachCall {

	public static boolean enforceLT(Domain dx, Domain dy) { // x < y
		return dx.removeValuesGreaterThanOrEqual(dy.lastValue()) && dy.removeValuesLessThanOrEqual(dx.firstValue());
	}

	public static boolean enforceLT(Domain dx, Domain dy, int k) { // x < y + k
		return dx.removeValuesGreaterThanOrEqual(dy.lastValue() + k) && dy.removeValuesLessThanOrEqual(dx.firstValue() - k);
	}

	// public static boolean enforceLT(Domain dx, int c, Domain dy) { // x < cy
	// return dx.removeValuesGreaterThanOrEqual(dy.lastValue() + k) && dy.removeValuesLessThanOrEqual(dx.firstValue() - k);
	// }

	public static boolean enforceLE(Domain dx, Domain dy) { // x <= y
		return dx.removeValuesGreaterThan(dy.lastValue()) && dy.removeValuesLessThan(dx.firstValue());
	}

	public static boolean enforceLE(Domain dx, Domain dy, int k) { // x <= y + k
		return dx.removeValuesGreaterThan(dy.lastValue() + k) && dy.removeValuesLessThan(dx.firstValue() - k);
	}

	// public static boolean enforceLE(Domain dx, int c, Domain dy, int k) { // x <= cy
	// return dx.removeValuesGreaterThan(k * (k < 0 ? dy.firstValue() : dy.lastValue())) && dy.removeValuesLessThan(dx.firstValue() - k);
	// }

	public static boolean enforceGE(Domain dx, Domain dy) { // x >= y
		return dx.removeValuesLessThan(dy.firstValue()) && dy.removeValuesGreaterThan(dx.lastValue());
	}

	public static boolean enforceGE(Domain dx, Domain dy, int k) { // x >= y + k
		return dx.removeValuesLessThan(dy.firstValue() + k) && dy.removeValuesGreaterThan(dx.lastValue() - k);
	}

	public static boolean enforceGT(Domain dx, Domain dy) { // x > y
		return dx.removeValuesLessThanOrEqual(dy.firstValue()) && dy.removeValuesGreaterThanOrEqual(dx.lastValue());
	}

	public static boolean enforceGT(Domain dx, Domain dy, int k) { // x > y + k
		return dx.removeValuesLessThanOrEqual(dy.firstValue() + k) && dy.removeValuesGreaterThanOrEqual(dx.lastValue() - k);
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

	public static boolean enforceEQ_summation(Domain dx, Domain dy, int k) { // x = y + k
		if (dx.removeValuesNotSummation(dy, k) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesNotSummation(dx, -k);
		assert consistent;
		return true;
	}

	public static boolean enforceEQ_multiple(Domain dx, Domain dy, int k) { // x = y * k
		if (dx.removeValuesNotMultiple(dy, k) == false)
			return false;
		if (dx.size() == dy.size())
			return true;
		assert dx.size() < dy.size();
		boolean consistent = dy.removeValuesNotDivisor(dx, k);
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

	public static boolean enforceNE_summation(Domain dx, Domain dy, int k) { // x != y + k
		if (dx.size() == 1 && dy.removeValueIfPresent(dx.uniqueValue() - k) == false)
			return false;
		if (dy.size() == 1 && dx.removeValueIfPresent(dy.uniqueValue() + k) == false)
			return false;
		return true;
	}

	public static boolean enforceNE_multiple(Domain dx, Domain dy, int k) { // x != y * k
		if (dx.size() == 1 && dx.uniqueValue() % k == 0 && dy.removeValueIfPresent(dx.uniqueValue() / k) == false)
			return false;
		if (dy.size() == 1 && dx.removeValueIfPresent(dy.uniqueValue() * k) == false)
			return false;
		return true;
	}

	public static int commonValueIn(Domain dx, Domain dy) {
		if (dx.size() <= dy.size())
			for (int a = dx.first(); a != -1; a = dx.next(a)) {
				int va = dx.toVal(a);
				if (dy.isPresentValue(va))
					return va;
			}
		else
			for (int b = dy.first(); b != -1; b = dy.next(b)) {
				int vb = dy.toVal(b);
				if (dx.isPresentValue(vb))
					return vb;
			}
		return Integer.MAX_VALUE;
	}

	// ************************************************************************
	// ***** Root classes and Disjonctive
	// ************************************************************************

	protected final Variable x, y;

	protected final Domain dx, dy;

	public CtrPrimitiveBinary(Problem pb, Variable x, Variable y) {
		super(pb, pb.api.vars(x, y));
		this.x = x;
		this.y = y;
		this.dx = x.dom;
		this.dy = y.dom;
	}

	public static abstract class CtrPrimitiveBinaryWithCst extends CtrPrimitiveBinary {

		protected final int k;

		public CtrPrimitiveBinaryWithCst(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y);
			this.k = k;
			defineKey(k);
		}
	}

	public static final class Disjonctive extends CtrPrimitiveBinary {

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
	// ***** Classes for x + y <op> k (CtrPrimitiveBinaryAdd)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryAdd extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryAdd(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		public static final class AddLE2 extends CtrPrimitiveBinaryAdd {

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

		public static final class AddGE2 extends CtrPrimitiveBinaryAdd {

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

		public static final class AddEQ2 extends CtrPrimitiveBinaryAdd implements TagUnsymmetric {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == k;
			}

			public AddEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesWhoseNegationNotIn(dy, -k) && dy.removeValuesWhoseNegationNotIn(dx, -k);
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
				if (dx.size() == 1 && dy.removeValueIfPresent(k - dx.uniqueValue()) == false)
					return false;
				if (dy.size() == 1 && dx.removeValueIfPresent(k - dy.uniqueValue()) == false)
					return false;
				return true;
			}
		}
	}
	// ************************************************************************
	// ***** Classes for x - y <op> k (CtrPrimitiveBinarySub)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinarySub extends CtrPrimitiveBinaryWithCst {

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
				return pb.addCtr(new SubEQ2(pb, x, y, k)); // return pb.extension(eq(sub(x, y), k));
			case NE:
				return pb.addCtr(new SubNE2(pb, x, y, k));
			}
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinarySub(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		public static final class SubLE2 extends CtrPrimitiveBinarySub implements TagUnsymmetric {

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

		public static final class SubGE2 extends CtrPrimitiveBinarySub implements TagUnsymmetric {

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
				return enforceEQ_summation(dx, dy, k);
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
				return enforceNE_summation(dx, dy, k);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> k (CtrPrimitiveBinaryMul)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryMul extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryMul(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
			control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
		}

		public static final class MulLE2 extends CtrPrimitiveBinaryMul {

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

		public static final class MulGE2 extends CtrPrimitiveBinaryMul {

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

		public static final class MulEQ2 extends CtrPrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] == k;
			}

			public MulEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k != 0);
				for (int a = dx.first(); a != -1; a = dx.next(a))
					if (dx.toVal(a) == 0 || k % dx.toVal(a) != 0) // no need to use absolute values when using %
						dx.removeAtConstructionTime(a);
				for (int b = dy.first(); b != -1; b = dy.next(b))
					if (dy.toVal(b) == 0 || k % dy.toVal(b) != 0)
						dy.removeAtConstructionTime(b);
			}

			private boolean revise(Domain d1, Domain d2) {
				int sizeBefore = d1.size();
				for (int a = d1.first(); a != -1; a = d1.next(a))
					if (d2.isPresentValue(k / d1.toVal(a)) == false)
						d1.removeElementary(a);
				return d1.afterElementaryCalls(sizeBefore);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return revise(dx, dy) && revise(dy, dx);
			}
		}

		public static final class MulNE2 extends CtrPrimitiveBinaryMul {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] * t[1] != k;
			}

			public MulNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k != 0);
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

	public static abstract class CtrPrimitiveBinaryMulb extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryMulb(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(Utilities.isSafeInt(BigInteger.valueOf(dy.firstValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
			control(Utilities.isSafeInt(BigInteger.valueOf(dy.lastValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
		}

		public static final class MulbEQ2 extends CtrPrimitiveBinaryMulb {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] == k * t[1];
			}

			public MulbEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				for (int a = dx.first(); a != -1; a = dx.next(a)) // values not multiple are deleted (important for filtering: avoid systematic check)
					if (dx.toVal(a) != 0 && dx.toVal(a) % k != 0)
						dx.removeAtConstructionTime(a);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return enforceEQ_multiple(dx, dy, k);
			}
		}

		public static final class MulbNE2 extends CtrPrimitiveBinaryMulb {

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
				return enforceNE_multiple(dx, dy, k);
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x / y <op> k (CtrPrimitiveBinaryDiv)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryDiv extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

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
			// return pb.addCtr(new DivNE2(pb, x, y, k));
			}
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryDiv(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
		}

		public static final class DivLE2 extends CtrPrimitiveBinaryDiv {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] <= k;
			}

			public DivLE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesNumeratorsGT(k, dy.lastValue()) && dy.removeValuesDenumeratorsGT(k, dx.firstValue());
			}
		}

		public static final class DivGE2 extends CtrPrimitiveBinaryDiv {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] >= k;
			}

			public DivGE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesNumeratorsLT(k, dy.firstValue()) && dy.removeValuesDenumeratorsLT(k, dx.lastValue());
			}
		}

		// Be careful: x/y = k is not equivalent to x/k = y (for example, 13/5 = 2 while 13/2 = 6)
		public static final class DivEQ2 extends CtrPrimitiveBinaryDiv {

			int[] resx, resy;

			@Override
			public boolean checkValues(int[] t) {
				return t[0] / t[1] == k;
			}

			public DivEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.resx = new int[dx.initSize()];
				this.resy = new int[dy.initSize()];
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if ((dx.lastValue() / dy.firstValue() < k) || (dx.firstValue() / dy.lastValue() > k)) // possible because only positive values
					return dx.fail();
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (dy.isPresent(resx[a]) && va / dy.toVal(resx[a]) == k)
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int res = va / dy.toVal(b);
						if (res < k)
							break;
						if (res == k) {
							resx[a] = b;
							continue extern;
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (dx.isPresent(resy[b]) && dx.toVal(resy[b]) / vb == k)
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(b)) {
						int res = dx.toVal(a) / vb;
						if (res > k)
							break;
						if (res == k) {
							resy[b] = a;
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

	public static abstract class CtrPrimitiveBinaryMod extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new ModEQ2(pb, x, y, k));
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryMod(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
		}

		public static final class ModEQ2 extends CtrPrimitiveBinaryMod {

			@Override
			public boolean checkValues(int[] t) {
				return t[0] % t[1] == k;
			}

			int[] resx, resy; // residues for values in the domains of x, and y

			public ModEQ2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				this.resx = Kit.repeat(-1, dx.initSize());
				this.resy = Kit.repeat(-1, dy.initSize());
				for (int a = dx.first(); a != -1; a = dx.next(a))
					if (dx.toVal(a) < k) // the remainder is at most k-1, whatever the value for y
						dx.removeAtConstructionTime(a);
					else
						break;
				for (int b = dy.first(); b != -1; b = dy.next(b))
					if (dy.toVal(b) <= k) // the remainder is at most k-1, whatever the value for x
						dy.removeAtConstructionTime(b);
					else
						break;
				// note that k is always supported, whatever the remaining value in y
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (va == k)
						continue; // because dy.lastValue() > k by construction (see constructor), and so there is a support
					if (resx[a] != -1 && dy.isPresent(resx[a]))
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (va % vb == k) {
							resx[a] = b;
							continue extern;
						} else {
							if (va < vb) // means that the remainder with remaining values of y always lead to va (and it is not k)
								break;
							// here, we know that va >= vb and va != k (see code earlier)
							if (va < 2 * vb) { // it means that the quotient was 1, and will remain 1 (and 0 later)
								assert va / vb == 1;
								if (va - k <= vb || dy.isPresentValue(va - k) == false)
									break;
								resx[a] = dy.toVal(va - k);
								continue extern;
							}
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (resy[b] != -1 && dx.isPresent(resy[b]))
						continue;
					int nMultiples = dx.size() / vb;
					if (dx.size() <= nMultiples) {
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int va = dx.toVal(a);
							if (va % vb == k) {
								resy[b] = a;
								continue extern;
							}
						}
					} else {
						// we know that vb > k by construction
						int va = vb + k;
						while (va <= dx.lastValue()) {
							assert va % vb == k;
							if (dx.isPresentValue(va)) {
								resy[b] = dx.toIdx(va);
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

	public static abstract class CtrPrimitiveBinaryDist extends CtrPrimitiveBinaryWithCst implements TagSymmetric {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryDist(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(k > 0, "k should be strictly positive");
		}

		public static final class DistLE2 extends CtrPrimitiveBinaryDist {

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

		public static final class DistGE2 extends CtrPrimitiveBinaryDist { // code similar to Disjunctive

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

		public static final class DistEQ2 extends CtrPrimitiveBinaryDist {

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

		public static final class DistNE2 extends CtrPrimitiveBinaryDist {

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) != k;
			}

			public DistNE2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			private boolean revise(Domain d1, Domain d2) {
				if (d1.size() == 1)
					return d2.removeValueIfPresent(d1.uniqueValue() - k) && d2.removeValueIfPresent(d1.uniqueValue() + k);
				if (d1.size() == 2 && d1.intervalValue() == 2 * k)
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
	// ***** Classes for x = (y <op> k) (CtrPrimitiveBinaryLog)
	// ************************************************************************

	public static abstract class CtrPrimitiveBinaryLog extends CtrPrimitiveBinaryWithCst implements TagUnsymmetric {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveBinaryLog(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			control(dx.is01(), "The first variable should be of type 01");
		}

		public static final class LogLE2 extends CtrPrimitiveBinaryLog {

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
				if (dx.first() == 1 && dy.lastValue() > k && dy.removeValuesGreaterThan(k) == false)
					return false;
				if (dx.last() == 0 && dy.firstValue() <= k && dy.removeValuesLessThanOrEqual(k) == false)
					return false;
				return true;
			}
		}

		public static final class LogGE2 extends CtrPrimitiveBinaryLog {

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
				if (dx.first() == 1 && dy.firstValue() < k && dy.removeValuesLessThan(k) == false)
					return false;
				if (dx.last() == 0 && dy.lastValue() >= k && dy.removeValuesGreaterThanOrEqual(k) == false)
					return false;
				return true;
			}
		}

		public static final class LogEQ2 extends CtrPrimitiveBinaryLog {

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

		public static final class LogNE2 extends CtrPrimitiveBinaryLog {

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
