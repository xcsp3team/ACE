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

import static utility.Kit.control;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeArithmeticOperator;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeUnaryArithmeticOperator;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNodeParent;

import constraints.Constraint;
import constraints.ConstraintExtension;
import constraints.ConstraintIntension;
import constraints.ConstraintSpecific;
import constraints.global.Sum.SumWeighted;
import constraints.intension.Primitive2.PrimitiveBinaryNoCst.Neg2EQ;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Add2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Dist2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Div2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mod2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Mul2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant1.Sub2;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Dist2b;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Dist2b.Dist2bEQ;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Div2b;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Mod2b;
import constraints.intension.Primitive2.PrimitiveBinaryVariant2.Mul2b;
import constraints.intension.Primitive2.PropagatorEQ.MultiPropagatorEQ;
import constraints.intension.Primitive2.PropagatorEQ.SimplePropagatorEQ;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagNotSymmetric;
import interfaces.Tags.TagPrimitive;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import propagation.AC;
import propagation.AC.TypeFilteringResult;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This class contains many propagators for binary primitive constraints such as for example:
 * <ul>
 * <li>x < y</li>
 * <li>x*y = 10</li>
 * <li>|x-y| <2</li>
 * </ul>
 * Important: in Java, integer division rounds toward 0. This implies that: 10/3 = 3, -10/3 = -3, 10/-3 = -3, -10/-3 = 3; see
 * https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.17.2
 * 
 * @author Christophe Lecoutre
 */
public abstract class Primitive2 extends ConstraintSpecific implements TagAC, TagCallCompleteFiltering, TagPrimitive {

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	public static final int UNITIALIZED = -1;

	public static Constraint buildFrom(Problem pb, Variable x, TypeUnaryArithmeticOperator uaop, Variable y) {
		switch (uaop) {
		case ABS: // x = |y|
			return new Dist2bEQ(pb, x, y, 0);
		case NEG: // x = -y
			return new Neg2EQ(pb, x, y); // TODO why not using x + y = 0 instead (one less propagator)?
		case SQR: // x = y*y
			List<int[]> table = new ArrayList<>();
			for (int a = y.dom.first(); a != -1; a = y.dom.next(a)) {
				int v = y.dom.toVal(a), vv = Utilities.safeInt((long) v * v);
				if (vv <= x.dom.greatestInitialValue() && x.dom.containsValue(vv))
					table.add(new int[] { vv, v });
			}
			return ConstraintExtension.buildFrom(pb, pb.vars(x, y), table, true, Boolean.FALSE);
		case NOT: // x = not(y)
			control(y.dom.is01()); // && y.dom.is01());
			if (!x.dom.is01())
				return null;
			return ConstraintExtension.buildFrom(pb, pb.vars(x, y), new int[][] { { 0, 1 }, { 1, 0 } }, true, Boolean.FALSE);

		default:
			throw new AssertionError("not possible");
		}
	}

	public static Constraint buildFrom(Problem pb, Variable x, TypeArithmeticOperator aop, Variable y, TypeConditionOperatorRel op, int k) {
		switch (aop) {
		case ADD:
			return Add2.buildFrom(pb, x, y, op, k);
		case SUB:
			return Sub2.buildFrom(pb, x, y, op, k);
		case MUL:
			return Mul2.buildFrom(pb, x, y, op, k);
		case DIV:
			return Div2.buildFrom(pb, x, y, op, k);
		case MOD:
			return Mod2.buildFrom(pb, x, y, op, k);
		case DIST:
			return Dist2.buildFrom(pb, x, y, op, k);
		default: // POW
			List<int[]> table = new ArrayList<>();
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				int v = x.dom.toVal(a);
				for (int b = y.dom.first(); b != -1; b = y.dom.next(b)) {
					int w = y.dom.toVal(b);
					double p = Math.pow(v, w);
					int pi = (int) p;
					if (pi == p && op.isValidFor(pi, k))
						table.add(new int[] { v, w });
				}
			}
			return ConstraintExtension.buildFrom(pb, pb.vars(x, y), table, true, Boolean.FALSE);
		}
	}

	public static Constraint buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, TypeArithmeticOperator aop, int k) {
		switch (aop) {
		case ADD:
			return Sub2.buildFrom(pb, x, y, op, k);
		case SUB:
			return Sub2.buildFrom(pb, x, y, op, -k);
		case MUL:
			return Mul2b.buildFrom(pb, x, op, y, k);
		case DIV:
			return Div2b.buildFrom(pb, x, op, y, k);
		case MOD:
			return Mod2b.buildFrom(pb, x, op, y, k);
		case DIST:
			return Dist2b.buildFrom(pb, x, op, y, k);
		default: // case POW:
			List<int[]> table = new ArrayList<>();
			for (int a = y.dom.first(); a != -1; a = y.dom.next(a)) {
				int v = y.dom.toVal(a), vv = Utilities.safeInt((long) Math.pow(v, k));
				if (x.dom.smallestInitialValue() <= vv && vv <= x.dom.greatestInitialValue() && x.dom.containsValue(vv))
					table.add(new int[] { vv, v });
			}
			return ConstraintExtension.buildFrom(pb, pb.vars(x, y), table, true, Boolean.FALSE);
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * The first variable involved in the binary primitive constraint
	 */
	protected final Variable x;

	/**
	 * The second variable involved in the binary primitive constraint
	 */
	protected final Variable y;

	/**
	 * The constant used in the binary primitive constraint. Note that it is not relevant for a few subclasses (propagators).
	 */
	protected final int k;

	/**
	 * The domain of x, the first involved variable
	 */
	protected final Domain dx;

	/**
	 * The domain of y, the second involved variable
	 */
	protected final Domain dy;

	/**
	 * Residues used for (value indexes of) x (possibly, null)
	 */
	protected int[] rx;

	/**
	 * Residues used for (value indexes of) y (possibly, null)
	 */
	protected int[] ry;

	/**
	 * Builds the structures of residues for x and y, the two involved variables
	 */
	protected void buildResiduesForBothVariables() {
		this.rx = Kit.repeat(UNITIALIZED, dx.initSize());
		this.ry = Kit.repeat(UNITIALIZED, dy.initSize());
	}

	/**
	 * Builds a binary primitive constraint for the specified problem with the two specified variables and the specified constant
	 * 
	 * @param pb
	 *            the problem to which the binary primitive constraint is attached
	 * @param x
	 *            the first variable of the binary primitive
	 * @param y
	 *            the second variable of the binary primitive
	 * @param k
	 *            the constant involved in the binary primitive (possible, 0)
	 */
	public Primitive2(Problem pb, Variable x, Variable y, int k) {
		super(pb, pb.api.vars(x, y));
		control(scp.length == 2);
		this.x = x;
		this.y = y;
		this.k = k;
		this.dx = x.dom;
		this.dy = y.dom;
		if (!(this instanceof PrimitiveBinaryNoCst))
			defineKey(k); // otherwise irrelevant
	}

	/**********************************************************************************************
	 * Classes where no constant is involved
	 *********************************************************************************************/

	public static abstract class PrimitiveBinaryNoCst extends Primitive2 {

		private static final int DUMMY = 0;

		public PrimitiveBinaryNoCst(Problem pb, Variable x, Variable y) {
			super(pb, x, y, DUMMY);
		}

		public static final class Disjonctive extends PrimitiveBinaryNoCst {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] + wx <= t[1] || t[1] + wy <= t[0];
			}

			private final int wx, wy;

			@Override
			public Boolean isSymmetric() {
				return wx == wy;
			}

			public Disjonctive(Problem pb, Variable x, int wx, Variable y, int wy) {
				super(pb, x, y);
				this.wx = wx;
				this.wy = wy;
				defineKey(wx, wy);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				return dx.removeValuesInRange(dy.lastValue() - wx + 1, dy.firstValue() + wy)
						&& dy.removeValuesInRange(dx.lastValue() - wy + 1, dx.firstValue() + wx);
			}
		}

		public static final class Neg2EQ extends PrimitiveBinaryNoCst implements TagNotSymmetric {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] == -t[1];
			}

			private final SimplePropagatorEQ sp;

			public Neg2EQ(Problem pb, Variable x, Variable y) {
				super(pb, x, y);
				this.sp = new SimplePropagatorEQ(dx, dy, true) {
					@Override
					final int valxFor(int b) {
						return -dy.toVal(b);
					}

					@Override
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

		public static final class Or2 extends PrimitiveBinaryNoCst {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] == 1 || t[1] == 1;
			}

			public Or2(Problem pb, Variable x, Variable y) {
				super(pb, x, y);
				assert x.dom.is01() && y.dom.is01();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1) {
					if (dx.single() == 0 && dy.removeIfPresent(0) == false)
						return false;
					return entail();
				}
				if (dy.size() == 1) {
					if (dy.single() == 0 && dx.removeIfPresent(0) == false)
						return false;
					return entail();
				}
				return true;
			}
		}

	}

	public static final class BoundEQSquare extends ConstraintSpecific implements TagNotAC, TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] == t[1] * t[1]; // x = y * y
		}

		public BoundEQSquare(Problem pb, Variable x, Variable y) {
			super(pb, pb.vars(x, y));
			this.dx = x.dom;
			this.dy = y.dom;
		}

		private final Domain dx, dy;

		@Override
		public boolean runPropagator(Variable dummy) {
			// dealing with min bounds
			int v = dx.firstValue(), w = dy.firstValue();
			while (v != w * w) {
				if (v < w * w) {
					if (dx.removeValuesLT(w * w) == false)
						return false;
					v = dx.firstValue();
				} else {
					assert v > w * w;
					break;
					// if (dy.removeValuesLT((int) Math.floor(Math.sqrt(v))) == false)
					// return false;
					// w = dy.firstValue();
				}
			}
			// dealing with max bounds
			v = dx.lastValue();
			w = dy.lastValue();
			while (v != w * w) {
				if (v > w * w) {
					if (dx.removeValuesGT(w * w) == false)
						return false;
					v = dx.lastValue();
				} else {
					assert v < w * w;
					break;
					// if (dy.removeValuesGT((int) Math.floor(Math.sqrt(v))) == false)
					// return false;
					// w = dy.lastValue();
				}
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * Auxiliary classes used in some primitive propagators
	 *********************************************************************************************/

	public abstract static class PropagatorEQ {

		protected final Domain dx, dy;

		protected int time;

		protected final int[] times;

		protected final boolean twoway;

		protected PropagatorEQ(Domain dx, Domain dy, boolean twoway) {
			this.dx = dx;
			this.dy = dy;
			this.twoway = twoway;
			this.times = new int[twoway ? Math.max(dx.initSize(), dy.initSize()) : dx.initSize()];
		}

		protected PropagatorEQ(Domain dx, Domain dy) {
			this(dx, dy, false);
		}

		protected abstract int nSupportsForWhenIteratingOver(Domain d1, Domain d2);

		private boolean runPropagator(Variable evt, Domain d1, Domain d2) {
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

		public final boolean runPropagator(Variable evt) {
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

			@Override
			protected final int nSupportsForWhenIteratingOver(Domain d1, Domain d2) {
				if (d2.size() == 1 && !d1.containsValue(d1 == dx ? valxFor(d2.single()) : valyFor(d2.single())))
					return 0;
				int cnt = 0;
				for (int b = d2.first(); b != -1; b = d2.next(b)) {
					int a = d1.toIdxIfPresent(d1 == dx ? valxFor(b) : valyFor(b));
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

			@Override
			protected final int nSupportsForWhenIteratingOver(Domain d1, Domain d2) {
				int cnt = 0;
				for (int b = d2.first(); b != -1; b = d2.next(b)) {
					boolean found = false;
					for (int va : d1 == dx ? valsxFor(b) : valsyFor(b)) {
						int a = d1.toIdxIfPresent(va);
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

	/**********************************************************************************************
	 * Variants number 1 of the binary primitives: here, the two variables are on the same side
	 *********************************************************************************************/

	public static abstract class PrimitiveBinaryVariant1 extends Primitive2 {

		public PrimitiveBinaryVariant1(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		// ************************************************************************
		// ***** Classes for x + y <op> k
		// ************************************************************************

		public static abstract class Add2 extends PrimitiveBinaryVariant1 implements TagSymmetric {

			public static Add2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Add2LE(pb, x, y, k - 1);
				case LE:
					return new Add2LE(pb, x, y, k);
				case GE:
					return new Add2GE(pb, x, y, k);
				case GT:
					return new Add2GE(pb, x, y, k + 1);
				case EQ:
					return new Add2EQ(pb, x, y, k); // return pb.extension(eq(add(x, y), k));
				default: // NE
					return new Add2NE(pb, x, y, k);
				}
			}

			public Add2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			public static final class Add2LE extends Add2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] + t[1] <= k;
				}

				public Add2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return AC.enforceAddLE(dx, dy, k);
				}
			}

			public static final class Add2GE extends Add2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] + t[1] >= k;
				}

				public Add2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return AC.enforceAddGE(dx, dy, k);
				}
			}

			public static final class Add2EQ extends Add2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] + t[1] == k;
				}

				private final SimplePropagatorEQ sp;

				public Add2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					this.sp = new SimplePropagatorEQ(dx, dy, true) {
						@Override
						final int valxFor(int b) {
							return k - dy.toVal(b);
						}

						@Override
						final int valyFor(int a) {
							return k - dx.toVal(a);
						}
					};
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					// return sp.runPropagator(dummy);
					return AC.enforceEQb(dx, dy, k); // new algo
				}
			}

			public static final class Add2NE extends Add2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] + t[1] != k;
				}

				public Add2NE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1)
						return dy.removeValueIfPresent(k - dx.singleValue());
					if (dy.size() == 1)
						return dx.removeValueIfPresent(k - dy.singleValue());
					return true;
				}
			}
		}
		// ************************************************************************
		// ***** Classes for x - y <op> k
		// ************************************************************************

		public static abstract class Sub2 extends PrimitiveBinaryVariant1 {

			public static Primitive2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Sub2LE(pb, x, y, k - 1);
				case LE:
					return new Sub2LE(pb, x, y, k);
				case GE:
					return new Sub2GE(pb, x, y, k);
				case GT:
					return new Sub2GE(pb, x, y, k + 1);
				case EQ:
					return new Sub2EQ(pb, x, y, k); // return pb.extension(eq(sub(x, y), k));
				default: // NE
					return new Sub2NE(pb, x, y, k);
				}
			}

			public Sub2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
			}

			public static final class Sub2LE extends Sub2 implements TagNotSymmetric {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] - t[1] <= k;
				}

				public Sub2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (AC.enforceLE(dx, dy, k) == false)
						return false;
					if (dx.lastValue() <= k + dy.firstValue())
						return entail();
					return true;
				}
			}

			public static final class Sub2GE extends Sub2 implements TagNotSymmetric {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] - t[1] >= k;
				}

				public Sub2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (AC.enforceGE(dx, dy, k) == false)
						return false;
					if (dx.firstValue() >= k + dy.lastValue())
						return entail();
					return true;
				}
			}

			public static final class Sub2EQ extends Sub2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] - t[1] == k;
				}

				@Override
				public Boolean isSymmetric() {
					return k == 0;
				}

				// private final SimplePropagatorEQ sp;

				public Sub2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					// this.sp = new SimplePropagatorEQ(dx, dy, true) {
					// @Override
					// final int valxFor(int b) {
					// return k + dy.toVal(b);
					// }
					//
					// @Override
					// final int valyFor(int a) {
					// return dx.toVal(a) - k;
					// }
					// };
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					// return sp.runPropagator(dummy);
					return AC.enforceEQ(dx, dy, k); // new algo
				}
			}

			public static final class Sub2NE extends Sub2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] - t[1] != k;
				}

				public Sub2NE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public Boolean isSymmetric() {
					return k == 0;
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1)
						return dy.removeValueIfPresent(dx.singleValue() - k) && entail();
					if (dy.size() == 1)
						return dx.removeValueIfPresent(dy.singleValue() + k) && entail();
					return true;
					// return enforceNE(dx, dy, k);
				}
			}
		}

		// ************************************************************************
		// ***** Classes for x * y <op> k
		// ************************************************************************

		public static abstract class Mul2 extends PrimitiveBinaryVariant1 implements TagSymmetric {

			public static Primitive2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Mul2LE(pb, x, y, k - 1);
				case LE:
					return new Mul2LE(pb, x, y, k);
				case GE:
					return new Mul2GE(pb, x, y, k);
				case GT:
					return new Mul2GE(pb, x, y, k + 1);
				case EQ:
					return new Mul2EQ(pb, x, y, k);
				default: // NE
					return new Mul2NE(pb, x, y, k);
				}
			}

			public Mul2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
				control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
			}

			public static final class Mul2LE extends Mul2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] * t[1] <= k;
				}

				public Mul2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				public static boolean revise(Domain d1, Domain d2, int k) {
					if (d2.containsValue(0)) {
						if (0 <= k)
							return true;
						if (d2.removeValue(0) == false)
							return false;
					}
					assert !d2.containsValue(0);
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

			public static final class Mul2GE extends Mul2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] * t[1] >= k;
				}

				public Mul2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				public static boolean revise(Domain d1, Domain d2, int k) {
					if (d2.containsValue(0)) {
						if (0 >= k)
							return true;
						if (d2.removeValue(0) == false)
							return false;
					}
					assert !d2.containsValue(0);
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

			public static final class Mul2EQ extends Mul2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] * t[1] == k;
				}

				private final SimplePropagatorEQ sp;

				public Mul2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					control(k > 1, "if k is 0 or 1, other constraints should be posted");
					// TODO could we just impose k != 0?
					dx.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
					dy.removeValuesAtConstructionTime(v -> v == 0 || k % v != 0);
					this.sp = new SimplePropagatorEQ(dx, dy, true) {
						@Override
						final int valxFor(int b) {
							return k / dy.toVal(b);
						}

						@Override
						final int valyFor(int a) {
							return k / dx.toVal(a);
						}
					};
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return sp.runPropagator(dummy);
					// return dx.removeValuesInvNotIn(dy, k) && dy.removeValuesInvNotIn(dx, k);
				}
			}

			public static final class Mul2NE extends Mul2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] * t[1] != k;
				}

				public Mul2NE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					control(k > 1, "if k is 0 or 1, other constraints should be posted");
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1) {
						int va = dx.singleValue();
						if (va != 0 && k % va == 0)
							return dy.removeValueIfPresent(k / va);
					} else if (dy.size() == 1) {
						int vb = dy.singleValue();
						if (vb != 0 && k % vb == 0)
							return dx.removeValueIfPresent(k / vb);
					}
					return true;
				}
			}
		}

		// ************************************************************************
		// ***** Classes for x / y <op> k
		// ************************************************************************

		public static abstract class Div2 extends PrimitiveBinaryVariant1 implements TagNotSymmetric {

			public static Div2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Div2LE(pb, x, y, k - 1);
				case LE:
					return new Div2LE(pb, x, y, k);
				case GE:
					return new Div2GE(pb, x, y, k);
				case GT:
					return new Div2GE(pb, x, y, k + 1);
				case EQ:
					return new Div2EQ(pb, x, y, k);
				default: // NE
					throw new AssertionError("not implemented"); // TODO interesting?
				}
			}

			public Div2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				if (dy.containsValue(0))
					dy.removeValueAtConstructionTime(0);
				control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
			}

			public static final class Div2LE extends Div2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] / t[1] <= k;
				}

				public Div2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return AC.enforceDivLE(dx, dy, k);
				}
			}

			public static final class Div2GE extends Div2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] / t[1] >= k;
				}

				public Div2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return AC.enforceDivGE(dx, dy, k);
				}
			}

			// Be careful: x/y = k is not equivalent to x/k = y (for example, 13/5 = 2 while 13/2 = 6)
			public static final class Div2EQ extends Div2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] / t[1] == k;
				}

				public Div2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					buildResiduesForBothVariables();
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if ((dx.lastValue() / dy.firstValue() < k) || (dx.firstValue() / dy.lastValue() > k))
						// possible because only positive values
						return dx.fail();
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (rx[a] != UNITIALIZED && dy.contains(rx[a]))
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
						if (ry[b] != UNITIALIZED && dx.contains(ry[b]))
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
		// ***** Classes for x % y <op> k
		// ************************************************************************

		public static abstract class Mod2 extends PrimitiveBinaryVariant1 implements TagNotSymmetric {

			public static Mod2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case EQ:
					return new Mod2EQ(pb, x, y, k);
				default:
					throw new AssertionError("not implemented"); // TODO relevant to implement the others?
				}
			}

			public Mod2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(dx.firstValue() >= 0 && dy.firstValue() > 0 && k >= 0);
			}

			public static final class Mod2EQ extends Mod2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] % t[1] == k;
				}

				public Mod2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					buildResiduesForBothVariables();
					dx.removeValuesAtConstructionTime(v -> v < k);
					// above, because the remainder is at most k-1, whatever the value of y
					dy.removeValuesAtConstructionTime(v -> v <= k);
					// above, because the remainder is at most k-1, whatever the value for x
					// note that k for x is always supported, whatever the remaining value in y
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						if (rx[a] != UNITIALIZED && dy.contains(rx[a]))
							continue;
						int va = dx.toVal(a);
						if (va == k)
							continue; // because dy.lastValue() > k by construction (see constructor), and so there is a support
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vb = dy.toVal(b);
							if (va % vb == k) {
								rx[a] = b;
								continue extern;
							}
							if (va < vb) // means that the remainder with remaining values of y always lead to va
								break;
							// here, we know that va >= vb and va != k (see code earlier)
							if (va < 2 * vb) { // it means that the quotient was 1, and will remain 1 (and 0 later)
								assert va / vb == 1;
								if (va - k <= vb || dy.containsValue(va - k) == false)
									break;
								rx[a] = dy.toIdx(va - k);
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						if (ry[b] != UNITIALIZED && dx.contains(ry[b]))
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
							int va = k;
							while (va <= dx.lastValue()) {
								assert va % vb == k;
								if (dx.containsValue(va)) {
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
		// ***** Classes for |x - y| <op> k
		// ************************************************************************

		public static abstract class Dist2 extends PrimitiveBinaryVariant1 implements TagSymmetric {

			public static Dist2 buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, int k) {
				switch (op) {
				case LT:
					return new Dist2LE(pb, x, y, k - 1); // return pb.extension(lt(dist(x, y), k));
				case LE:
					return new Dist2LE(pb, x, y, k); // return pb.extension(le(dist(x, y), k));
				case GE:
					return new Dist2GE(pb, x, y, k);
				case GT:
					return new Dist2GE(pb, x, y, k + 1);
				case EQ:
					return new Dist2EQ(pb, x, y, k); // return pb.extension(eq(dist(x, y), k));
				// TODO ok for java ace csp/Rlfap-scen-11-f06.xml.lzma -varh=Dom -ev but not ok for -varh=WdegOnDom.
				// Must be because of conflict occurring on assigned variables in DISTEQ2
				default: // NE
					return new Dist2NE(pb, x, y, k);
				}
			}

			public Dist2(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k > 0, "k should be strictly positive");
			}

			public static final class Dist2LE extends Dist2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return Math.abs(t[0] - t[1]) <= k;
				}

				public Dist2LE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return dx.removeValuesAtDistanceGT(k, dy) && dy.removeValuesAtDistanceGT(k, dx);
				}
			}

			public static final class Dist2GE extends Dist2 { // code similar to Disjunctive

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return Math.abs(t[0] - t[1]) >= k;
					// equivalent to disjunctive: t[0] + k <= t[1] || t[1] + k <= t[0];
				}

				public Dist2GE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.lastValue() + k <= dy.firstValue() || dy.lastValue() + k <= dx.firstValue())
						return entail();
					return dx.removeValuesInRange(dy.lastValue() - k + 1, dy.firstValue() + k)
							&& dy.removeValuesInRange(dx.lastValue() - k + 1, dx.firstValue() + k);
				}
			}

			public static final class Dist2EQ extends Dist2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return Math.abs(t[0] - t[1]) == k;
				}

				private final MultiPropagatorEQ sp;

				public Dist2EQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					int[] tmp = new int[2];
					this.sp = new MultiPropagatorEQ(dx, dy, true) {
						@Override
						final int[] valsxFor(int b) {
							tmp[0] = dy.toVal(b) + k;
							tmp[1] = dy.toVal(b) - k;
							return tmp;
						}

						@Override
						final int[] valsyFor(int a) {
							tmp[0] = dx.toVal(a) + k;
							tmp[1] = dx.toVal(a) - k;
							return tmp;
						}
					};
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return sp.runPropagator(dummy);
					// return dx.removeValuesAtDistanceNE(k, dy) && dy.removeValuesAtDistanceNE(k, dx);
				}
			}

			public static final class Dist2NE extends Dist2 {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return Math.abs(t[0] - t[1]) != k;
				}

				public Dist2NE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				// private boolean revise(Domain d1, Domain d2) {
				// if (d1.size() == 1)
				// return d2.removeValueIfPresent(d1.singleValue() - k) && d2.removeValueIfPresent(d1.singleValue() + k) && entail();
				// if (d1.size() == 2 && d1.lastValue() - k == d1.firstValue() + k)
				// return d2.removeValueIfPresent(d1.lastValue() - k) ;
				// return true;
				// }

				@Override
				public boolean runPropagator(Variable dummy) {
					TypeFilteringResult res = AC.enforceDistNE(dx, dy, k);
					if (res == TypeFilteringResult.ENTAIL)
						return entail();
					assert res == TypeFilteringResult.TRUE || res == TypeFilteringResult.FALSE; // FAIL not possible
					return res == TypeFilteringResult.TRUE;
					// return revise(dx, dy) && revise(dy, dx);
				}
			}
		}
	}

	/**********************************************************************************************
	 * Variants number 2 of the binary primitives: here, the two variables are not on the same side
	 *********************************************************************************************/

	public static abstract class PrimitiveBinaryVariant2 extends Primitive2 implements TagNotSymmetric {

		public PrimitiveBinaryVariant2(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		// ************************************************************************
		// ***** Classes for x <op> y * k
		// ************************************************************************

		public static abstract class Mul2b extends PrimitiveBinaryVariant2 {

			public static Constraint buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
				if (k == 0)
					return new ConstraintIntension(pb, new Variable[] { x }, XNodeParent.build(op.toExpr(), x, 0));
				switch (op) {
				case LT:
				case LE:
				case GE:
				case GT:
					// IMPORTANT: keep this order for the variables and the coefficients (must be in increasing order)
					return SumWeighted.buildFrom(pb, pb.vars(y, x), new int[] { -k, 1 }, op, 0);
				case EQ:
					if (k == 0)
						return new ConstraintIntension(pb, new Variable[] { x }, pb.api.eq(x, 0)); // TODO simplify
					return new Mul2bEQ(pb, x, y, k);
				default: // NE
					return new Mul2bNE(pb, x, y, k);
				}
			}

			public Mul2b(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(k != 0);
				control(Utilities.isSafeInt(BigInteger.valueOf(dy.firstValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
				control(Utilities.isSafeInt(BigInteger.valueOf(dy.lastValue()).multiply(BigInteger.valueOf(k)).longValueExact()));
			}

			public static final class Mul2bEQ extends Mul2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == t[1] * k;
				}

				private final SimplePropagatorEQ sp;

				public Mul2bEQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					dx.removeValuesAtConstructionTime(v -> v != 0 && v % k != 0); // non multiple deleted (important for
																					// avoiding systematic checks)
					this.sp = new SimplePropagatorEQ(dx, dy, true) {
						@Override
						final int valxFor(int b) {
							return dy.toVal(b) * k;
						}

						@Override
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

			public static final class Mul2bNE extends Mul2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] != t[1] * k;
				}

				public Mul2bNE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k); // note that values in x that are not multiple of k are always supported
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1)
						return dx.singleValue() % k != 0 || dy.removeValueIfPresent(dx.singleValue() / k);
					if (dy.size() == 1)
						return dx.removeValueIfPresent(dy.singleValue() * k);
					return true;
				}
			}
		}

		// ************************************************************************
		// ***** Classes for x <op> y / k
		// ************************************************************************

		public static abstract class Div2b extends PrimitiveBinaryVariant2 {

			public static Constraint buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
				if (k == 1)
					return new ConstraintIntension(pb, new Variable[] { x, y }, XNodeParent.build(op.toExpr(), x, y));
				control(k > 1, x + " " + op + " " + y + "/" + k); // || or k < 0 ?
				switch (op) {
				case LT:
					return k == 1 ? buildFrom(pb, x, op, y, TypeArithmeticOperator.ADD, 0) : new Div2bLT(pb, x, y, k);
				case LE:
					return new Div2bLE(pb, x, y, k);
				case GE:
					return new Div2bGE(pb, x, y, k);
				case GT:
					return new Div2bGT(pb, x, y, k);
				case EQ:
					if (x.dom.firstValue() >= 0 && y.dom.firstValue() >= 0 && k > 1)
						return new Div2bEQ(pb, x, y, k);
					break;
				case NE:
					if (x.dom.firstValue() >= 0 && y.dom.firstValue() >= 0 && k > 1)
						return new Div2bNE(pb, x, y, k);
					break;
				}
				XNodeParent<IVar> p = XNodeParent.build(op.toExpr(), x, XNodeParent.div(y, k));
				return new ConstraintIntension(pb, new Variable[] { x, y }, p); // TODO may be very costly
				// throw new AssertionError("not implemented");
			}

			public Div2b(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(dx.firstValue() >= 0 && dy.firstValue() >= 0 && k > 1, dx.firstValue() + " " + dy.firstValue() + " " + k);
			}

			public static final class Div2bLT extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] < t[1] / k;
				}

				public Div2bLT(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return dx.removeValuesGE(dy.lastValue() / k) && dy.removeValuesLE(dx.firstValue() * k + k - 1);

				}
			}

			public static final class Div2bLE extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] <= t[1] / k;
				}

				public Div2bLE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return dx.removeValuesGT(dy.lastValue() / k) && dy.removeValuesLT(dx.firstValue() * k);

				}
			}

			public static final class Div2bGE extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] >= t[1] / k;
				}

				public Div2bGE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return dx.removeValuesLT(dy.firstValue() / k) && dy.removeValuesGT(dx.lastValue() * k + k - 1);
				}
			}

			public static final class Div2bGT extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] > t[1] / k;
				}

				public Div2bGT(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					return dx.removeValuesLE(dy.firstValue() / k) && dy.removeValuesGE(dx.lastValue() * k);
				}
			}

			public static final class Div2bEQ extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == t[1] / k;
				}

				private final SimplePropagatorEQ sp;

				public Div2bEQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					this.sp = new SimplePropagatorEQ(dx, dy, false) {
						@Override
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

			public static final class Div2bNE extends Div2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] != t[1] / k;
				}

				public Div2bNE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1)
						return dy.removeValuesInRange(dx.singleValue() * k, dx.singleValue() * k + k);
					if (dy.firstValue() / k == dy.lastValue() / k)
						return dx.removeValueIfPresent(dy.firstValue() / k);
					return true;
				}
			}
		}

		// ************************************************************************
		// ***** Classes for x <op> y % k
		// ************************************************************************

		public static abstract class Mod2b extends PrimitiveBinaryVariant2 {

			public static Mod2b buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
				switch (op) {
				case EQ:
					return new Mod2bEQ(pb, x, y, k);
				case NE:
					return new Mod2bNE(pb, x, y, k);
				default:
					// not relevant to implement them? (since an auxiliary variable can be introduced?)
					throw new AssertionError("not implemented");
				}
			}

			public Mod2b(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(dx.firstValue() >= 0 && dy.firstValue() >= 0 && k > 1);
			}

			public static final class Mod2bEQ extends Mod2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == t[1] % k;
				}

				private final SimplePropagatorEQ sp;

				public Mod2bEQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					dx.removeValuesAtConstructionTime(v -> v >= k); // because the remainder is at most k-1, whatever
																	// the value of y
					this.sp = new SimplePropagatorEQ(dx, dy, false) {
						@Override
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

			public static final class Mod2bNE extends Mod2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] != t[1] % k;
				}

				public Mod2bNE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				int watch1 = -1, watch2 = -1; // watching two different value indexes of y leading to two different
												// remainders

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
					if (dx.size() == 1)
						return dy.removeValuesModIn(dx, k) && entail();
					if (watch1 == -1 || !dy.contains(watch1))
						watch1 = findWatch(watch2);
					if (watch1 == -1) { // watch2 is the only remaining valid watch (we know that it is still valid
										// since the domain is not empty)
						assert watch2 != -1 && dy.contains(watch2);
						return dx.removeValueIfPresent(dy.toVal(watch2) % k) && entail();
					}
					if (watch2 == -1 || !dy.contains(watch2))
						watch2 = findWatch(watch1);
					if (watch2 == -1)
						return dx.removeValueIfPresent(dy.toVal(watch1) % k) && entail();
					return true;
				}
			}
		}

		// ************************************************************************
		// ***** Classes for x <op> |y - k|
		// ************************************************************************

		public static abstract class Dist2b extends PrimitiveBinaryVariant2 {

			public static Dist2b buildFrom(Problem pb, Variable x, TypeConditionOperatorRel op, Variable y, int k) {
				switch (op) {
				case EQ:
					return new Dist2bEQ(pb, x, y, k);
				case NE:
					return new Dist2bNE(pb, x, y, k);
				default:
					// not relevant to implement them? (since an auxiliary variable can be introduced?)
					throw new AssertionError("not implemented");
				}
			}

			public Dist2b(Problem pb, Variable x, Variable y, int k) {
				super(pb, x, y, k);
				control(dx.firstValue() >= 0);
				control(k >= 0, "k should be positive or 0");

			}

			public static final class Dist2bEQ extends Dist2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] == Math.abs(t[1] - k);
				}

				private final SimplePropagatorEQ sp;

				public Dist2bEQ(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
					this.sp = new SimplePropagatorEQ(dx, dy, false) {
						@Override
						final int valxFor(int b) {
							return Math.abs(dy.toVal(b) - k);
						}
					};
				}

				@Override
				public boolean runPropagator(Variable evt) {
					if (dx.size() == 1 && !dy.containsValue(k + dx.singleValue()) && !dy.containsValue(k - dx.singleValue()))
						return evt.dom.fail();
					return sp.runPropagator(evt);
				}
			}

			public static final class Dist2bNE extends Dist2b {

				@Override
				public boolean isSatisfiedBy(int[] t) {
					return t[0] != Math.abs(t[1] - k);
				}

				public Dist2bNE(Problem pb, Variable x, Variable y, int k) {
					super(pb, x, y, k);
				}

				@Override
				public boolean runPropagator(Variable dummy) {
					if (dx.size() == 1)
						return dy.removeValueIfPresent(k + dx.singleValue()) && dy.removeValueIfPresent(k - dx.singleValue()) && entail();
					if (dy.size() == 1)
						return dx.removeValueIfPresent(Math.abs(dy.singleValue() - k)) && entail();
					if (dy.size() == 2) {
						int v = Math.abs(dy.firstValue() - k);
						if (Math.abs(dy.lastValue() - k) == v)
							return dx.removeValueIfPresent(v) && entail();
					}
					return true;
				}
			}
		}
	}

	// ************************************************************************
	// ***** Class for min(x,k-x) <= y
	// ************************************************************************

	public static class Min2kLE extends Primitive2 {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return Math.min(t[0], k - t[0]) <= t[1];
		}

		public Min2kLE(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dy.removeValuesLT(Math.min(dx.firstValue(), k - dx.lastValue())) == false)
				return false;
			if (dx.removeValuesInRange(dy.lastValue() + 1, k - dy.lastValue()) == false)
				return false;
			if (dy.firstValue() >= Math.min(dx.lastValue(), k - dx.firstValue()))
				return entail();
			return true;
		}
	}

	// ************************************************************************
	// ***** Class for x = max(y,k)
	// ************************************************************************

	public static class Max2kEQ extends Primitive2 {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] == Math.max(t[1], k);
		}

		public Max2kEQ(Problem pb, Variable x, Variable y, int k) {
			super(pb, x, y, k);
			dx.removeValuesAtConstructionTime(v -> v < k);
			control(dx.size() > 0);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			assert dx.firstValue() >= k;
			if (!dx.containsValue(k))
				if (dy.removeValuesLE(k) == false)
					return false;
			if (dy.lastValue() <= k)
				return dx.reduceToValue(k) && entail();
			if (dy.firstValue() >= k)
				return AC.enforceEQ(dx, dy);
			assert dx.containsValue(k);
			int currx = dx.last(), curry = dy.last();
			int valx = dx.toVal(currx), valy = dy.toVal(curry);
			while (valx > k || valy > k) {
				if (valx < valy) {
					if (dy.remove(curry) == false)
						return false;
					curry = dy.prev(curry);
					valy = dy.toVal(curry);
				} else if (valx > valy) {
					if (dx.remove(currx) == false)
						return false;
					currx = dx.prev(currx);
					valx = dx.toVal(currx);
				} else {
					curry = dy.prev(curry);
					valy = dy.toVal(curry);
					currx = dx.prev(currx);
					valx = dx.toVal(currx);
				}
			}
			return true;
		}
	}
}

// public static final class MulLE2Old extends PrimitiveBinaryMul {
//
// @Override
// public boolean isSatisfiedBy(int[] t) {
// return t[0] * t[1] <= k;
// }
//
// public MulLE2Old(Problem pb, Variable x, Variable y, int k) {
// super(pb, x, y, k);
// }
//
// private boolean checkLimit(int c, int k, Domain dom) { // c*y <= k
// if (c == 0)
// return k >= 0;
// int limit = Kit.greatestIntegerLE(c, k);
// return c > 0 ? dom.firstValue() <= limit : dom.lastValue() >= limit;
// }
//
// private boolean revise(Domain d1, Domain d2) {
// int sizeBefore = d1.size();
// for (int a = d1.last(); a != -1; a = d1.prev(a)) {
// int va = d1.toVal(a);
// if ((va > 0 && d2.firstValue() >= 0 && va * d2.firstValue() <= k) || (va < 0 && d2.lastValue() >= 0 && va *
// d2.lastValue() <= k))
// break; // because all values of d1 are necessarily supported
// if (checkLimit(va, k, d2))
// continue;
// d1.removeElementary(a);
// }
// return d1.afterElementaryCalls(sizeBefore);
// }
//
// @Override
// public boolean runPropagator(Variable dummy) {
// return revise(dx, dy) && revise(dy, dx);
// }
// }
//
// public static final class MulGE2Old extends PrimitiveBinaryMul {
//
// @Override
// public boolean isSatisfiedBy(int[] t) {
// return t[0] * t[1] >= k;
// }
//
// public MulGE2Old(Problem pb, Variable x, Variable y, int k) {
// super(pb, x, y, k);
// }
//
// private boolean checkLimit(int c, int k, Domain dom) { // c*y >= k
// if (c == 0)
// return k <= 0;
// int limit = Kit.smallestIntegerGE(c, k);
// return c > 0 ? dom.lastValue() >= limit : dom.firstValue() <= limit;
// }
//
// private boolean revise(Domain d1, Domain d2) {
// int sizeBefore = d1.size();
// for (int a = d1.first(); a != -1; a = d1.next(a)) {
// int va = d1.toVal(a);
// if ((va > 0 && d2.lastValue() >= 0 && va * d2.lastValue() >= k) || (va < 0 && d2.firstValue() >= 0 && va *
// d2.firstValue() >= k))
// break; // because all values of d1 are necessarily supported
// if (checkLimit(va, k, d2))
// continue;
// d1.removeElementary(a);
// }
// return d1.afterElementaryCalls(sizeBefore);
// }
//
// @Override
// public boolean runPropagator(Variable dummy) {
// return revise(dx, dy) && revise(dy, dx);
// }
// }

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
// assert dx.iterateOnValuesStoppingWhen(v -> v != 0 && v % k != 0) == false; // we assume that trivial inconsistent
// values have been deleted
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

// public static boolean enforceNE(Domain dx, Domain dy, int k) { // x != y + k
// if (dx.size() == 1)
// return dy.removeValueIfPresent(dx.uniqueValue() - k);
// if (dy.size() == 1)
// return dx.removeValueIfPresent(dy.uniqueValue() + k);
// return true;
// }