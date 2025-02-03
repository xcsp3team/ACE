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

import java.math.BigInteger;

import org.xcsp.common.Types.TypeArithmeticOperator;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.global.Sum.SumWeighted;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotCallCompleteFiltering;
import interfaces.Tags.TagNotSymmetric;
import problem.Problem;
import propagation.AC;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This class contains many propagators for ternary primitive constraints such as for example x + y = z, |x - y| > z or x%y = z <br />
 * Important: in Java, integer division rounds toward 0. <br/>
 * This implies that: 10/3 = 3, -10/3 = -3, 10/-3 = -3, -10/-3 = 3 <br />
 * See https://docs.oracle.com/javase/specs/jls/se8/html/jls-15.html#jls-15.17.2
 * 
 * @author Christophe Lecoutre
 */
public abstract class Primitive3 extends Primitive implements TagAC, TagCallCompleteFiltering, TagNotSymmetric {
	// TODO AC not true sometimes

	public static Constraint buildFrom(Problem pb, Variable x, TypeArithmeticOperator aop, Variable y, TypeConditionOperatorRel op, Variable z) {
		switch (aop) {
		case ADD:
			return Add3.buildFrom(pb, x, y, op, z);
		case SUB:
			return Sub3.buildFrom(pb, x, y, op, z);
		case MUL:
			return Mul3.buildFrom(pb, x, y, op, z);
		case DIV:
			return Div3.buildFrom(pb, x, y, op, z);
		case MOD:
			return Mod3.buildFrom(pb, x, y, op, z);
		case DIST:
			return Dist3.buildFrom(pb, x, y, op, z);
		default: // POW
			throw new AssertionError("not implemented"); // TODO interesting?
		}
	}

	/**
	 * The first variable involved in the ternary primitive constraint
	 */
	protected final Variable x;

	/**
	 * The second variable involved in the ternary primitive constraint
	 */
	protected final Variable y;

	/**
	 * The third variable involved in the ternary primitive constraint
	 */
	protected final Variable z;

	/**
	 * The domain of x, the first involved variable
	 */
	protected final Domain dx;

	/**
	 * The domain of y, the second involved variable
	 */
	protected final Domain dy;

	/**
	 * The domain of y, the third involved variable
	 */
	protected final Domain dz;

	/**
	 * Residues used for (value indexes of) x (possibly, null)
	 */
	protected int[] rx;

	/**
	 * Residues used for (value indexes of) y (possibly, null)
	 */
	protected int[] ry;

	/**
	 * Residues used for (value indexes of) z, targeted towards x
	 */
	protected int[] rzx;

	/**
	 * Residues used for (value indexes of) z, targeted towards y
	 */
	protected int[] rzy;

	/**
	 * Builds the structure of residues for x, y and z (only targeted towards x for z)
	 */
	protected void buildThreeResidueStructure() {
		this.rx = new int[dx.initSize()];
		this.ry = new int[dy.initSize()];
		this.rzx = new int[dz.initSize()];
	}

	/**
	 * Builds the structure of residues for x, y and z
	 */
	protected void buildFourResidueStructure() {
		this.rx = new int[dx.initSize()];
		this.ry = new int[dy.initSize()];
		this.rzx = Kit.repeat(-1, dz.initSize());
		this.rzy = Kit.repeat(-1, dz.initSize());
	}

	/**
	 * Builds a ternary primitive constraint for the specified problem with the three specified variables
	 * 
	 * @param pb
	 *            the problem to which the ternary primitive constraint is attached
	 * @param x
	 *            the first variable of the ternary primitive
	 * @param y
	 *            the second variable of the ternary primitive
	 * @param z
	 *            the third variable of the ternary primitive
	 */
	public Primitive3(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, pb.api.vars(x, y, z));
		this.x = x;
		this.y = y;
		this.z = z;
		this.dx = x.dom;
		this.dy = y.dom;
		this.dz = z.dom;
	}

	// ************************************************************************
	// ***** Classes for x + y <op> z
	// ************************************************************************

	public static abstract class Add3 extends Primitive3 implements TagNotCallCompleteFiltering {

		private static final int RUNNING_LIMIT = 200; // TODO hard coding_

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case EQ:
				return new Add3EQ(pb, x, y, z);
			default:
				// we order variables according to coeffs
				return SumWeighted.buildFrom(pb, pb.api.vars(z, x, y), pb.api.vals(-1, 1, 1), op, 0);
			}
		}

		public Add3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class Add3EQ extends Add3 { // O(d^2)

			boolean multidirectional = false; // hard coding

			@Override
			public boolean isGuaranteedAC() {
				return dx.size() * (double) dy.size() <= RUNNING_LIMIT;
			}

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] + t[1] == t[2];
			}

			public Add3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildThreeResidueStructure();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() == 1)
					return AC.enforceEQ(dz, dy, dx.singleValue());
				if (dy.size() == 1)
					return AC.enforceEQ(dz, dx, dy.singleValue());
				if (dz.size() == 1)
					return AC.enforceEQb(dx, dy, dz.singleValue());

				if (dx.size() * (double) dy.size() > RUNNING_LIMIT) {
					if (dz.removeValuesLT(dx.firstValue() + dy.firstValue()) == false || dz.removeValuesGT(dx.lastValue() + dy.lastValue()) == false)
						return false;
					return AC.enforceAddGE(dx, dy, dz.firstValue()) && AC.enforceAddLE(dx, dy, dz.lastValue());
				}
				boolean connexz = dz.connex();
				boolean avoidx = false, avoidy = false;
				if (connexz) {
					int minx = dx.firstValue(), maxx = dx.lastValue();
					int miny = dy.firstValue(), maxy = dy.lastValue();
					avoidx = dz.enclose(minx + miny, maxx + miny) || dz.enclose(minx + maxy, maxx + maxy);
					avoidy = dz.enclose(miny + minx, maxy + minx) || dz.enclose(miny + maxx, maxy + maxx);
				}
				if (!avoidx)
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (dy.contains(rx[a]) && dz.containsValue(va + dy.toVal(rx[a])))
							continue;
						if (dy.size() <= dz.size())
							for (int b = dy.first(); b != -1; b = dy.next(b)) {
								int vc = va + dy.toVal(b);
								if (vc > dz.lastValue())
									break;
								if (dz.containsValue(vc)) {
									rx[a] = b;
									if (multidirectional) {
										ry[b] = a;
										rzx[dz.toIdx(vc)] = a;
									}
									continue extern;
								}
							}
						else
							for (int c = dz.first(); c != -1; c = dz.next(c)) {
								int vb = dz.toVal(c) - va;
								if (vb > dy.lastValue())
									break;
								if (dy.containsValue(vb)) {
									rx[a] = dy.toIdx(vb);
									if (multidirectional) {
										ry[dy.toIdx(vb)] = a;
										rzx[c] = a;
									}
									continue extern;
								}
							}
						if (dx.remove(a) == false)
							return false;
					}

				if (!avoidy)
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (dx.contains(ry[b]) && dz.containsValue(vb + dx.toVal(ry[b])))
							continue;
						if (dx.size() <= dz.size())
							for (int a = dx.first(); a != -1; a = dx.next(a)) {
								int vc = vb + dx.toVal(a);
								if (vc > dz.lastValue())
									break;
								if (dz.containsValue(vc)) {
									ry[b] = a;
									if (multidirectional)
										rzx[dz.toIdx(vc)] = a;
									continue extern;
								}
							}
						else
							for (int c = dz.first(); c != -1; c = dz.next(c)) {
								int va = dz.toVal(c) - vb;
								if (va > dx.lastValue())
									break;
								if (dx.containsValue(va)) {
									ry[b] = dx.toIdx(va);
									if (multidirectional)
										rzx[c] = dx.toIdx(va);
									continue extern;
								}
							}
						if (dy.remove(b) == false)
							return false;
					}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (dx.contains(rzx[c]) && dy.containsValue(vc - dx.toVal(rzx[c])))
						continue;
					if (dx.size() <= dy.size())
						for (int a = dx.last(); a != -1; a = dx.prev(a)) {
							int vb = vc - dx.toVal(a);
							if (vb > dy.lastValue())
								break;
							if (dy.containsValue(vb)) {
								rzx[c] = a;
								continue extern;
							}
						}
					else
						for (int b = dy.last(); b != -1; b = dy.prev(b)) {
							int va = vc - dy.toVal(b);
							if (va > dx.lastValue())
								break;
							if (dx.containsValue(va)) {
								rzx[c] = dx.toIdx(va);
								continue extern;
							}
						}

					if (dz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x - y <op> z
	// ************************************************************************

	public static abstract class Sub3 extends Primitive3 {

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			return Add3.buildFrom(pb, y, z, op, x); // x - y op z is equivalent to y + z op x
		}

		public Sub3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> z
	// ************************************************************************

	public static abstract class Mul3 extends Primitive3 {

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case EQ:
				return x.dom.is01() ? new Mul3bEQ(pb, x, y, z) : y.dom.is01() ? new Mul3bEQ(pb, y, x, z) : new Mul3EQ(pb, y, x, z);
			default:
				throw new AssertionError("not implemented");
			}
		}

		public Mul3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class Mul3bEQ extends Mul3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public Mul3bEQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				control(dx.is01(), "The first variable should be of type 01");
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0 || dy.containsOnlyValue(0)) // x = 0 or y = 0 => z = 0
					return dz.reduceToValue(0);
				if (dz.containsOnlyValue(0)) { // if z = 0
					if (dx.first() == 0 && dy.containsValue(0)) // 0 in dx and 0 in dy => every value is supported
						return true;
					return dx.first() == 0 ? dx.reduceTo(0) : dy.reduceToValue(0); // if 0 not in dy => x must be 0,
																					// else => y must be 0
				}
				if (dz.containsValue(0)) { // if 0 in dz
					if (dx.first() == 1 && !dy.containsValue(0) && dz.removeValue(0) == false)
						return false;
				} else if (dx.removeIfPresent(0) == false || dy.removeValueIfPresent(0) == false)
					return false;

				if (dx.first() == 1) // x = 1 => y = z
					return AC.enforceEQ(dy, dz);

				assert dx.size() == 2 && dz.containsValue(0) && dz.size() > 1;
				// above, because if 0 not in z, dx.size() cannot be 2
				// every value of dy is supported (by both 0 in x and z); we still need to filter z (and possibly 1 out
				// of dx)

				int sizeBefore = dz.size();
				for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (vc != 0 && !dy.containsValue(vc))
						dz.removeElementary(c);
				}
				dz.afterElementaryCalls(sizeBefore);
				if (dz.size() == 1) {
					assert dz.containsOnlyValue(0);
					dx.remove(1); // no possible inconsistency
				}
				return true;
			}
		}

		public static final class Mul3EQ extends Mul3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public Mul3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
				control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
			}

			@Override
			public boolean isGuaranteedAC() {
				return false;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() * dy.size() > 200) { // hard coding // TODO what about AC Guaranteed?
					int v1 = dx.firstValue() * dy.firstValue(), v2 = dx.firstValue() * dy.lastValue();
					int v3 = dx.lastValue() * dy.firstValue(), v4 = dx.lastValue() * dy.lastValue();
					int min1 = Math.min(v1, v2), max1 = Math.max(v1, v2);
					int min2 = Math.min(v3, v4), max2 = Math.max(v3, v4);
					if (dz.removeValuesLT(Math.min(min1, min2)) == false || dz.removeValuesGT(Math.max(max1, max2)) == false)
						return false;
					return AC.enforceMulGE(dx, dy, dz.firstValue()) && AC.enforceMulLE(dx, dy, dz.lastValue());
				}
				if (!dy.containsValue(0) || !dz.containsValue(0))
					// if 0 is present in dy and dz, all values of x are supported
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va == 0) {
							if (!dz.containsValue(0) && dx.remove(a) == false)
								return false;
							continue;
						}
						if (dy.contains(rx[a]) && dz.containsValue(va * dy.toVal(rx[a])))
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va * dy.toVal(b);
							if ((va > 0 && vc > dz.lastValue()) || (va < 0 && vc < dz.firstValue()))
								break;
							if (dz.containsValue(vc)) {
								rx[a] = b;
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
				if (!dx.containsValue(0) || !dz.containsValue(0))
					// if 0 is present in dx and dz, all values of y are supported
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (vb == 0) {
							if (!dz.containsValue(0) && dy.remove(b) == false)
								return false;
							continue;
						}
						if (dx.contains(ry[b]) && dz.containsValue(vb * dx.toVal(ry[b])))
							continue;
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = vb * dx.toVal(a);
							if ((vb > 0 && vc > dz.lastValue()) || (vb < 0 && vc < dz.firstValue()))
								break;
							if (dz.containsValue(vc)) {
								ry[b] = a;
								continue extern;
							}
						}
						if (dy.remove(b) == false)
							return false;
					}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (vc == 0) {
						if (!dx.containsValue(0) && !dy.containsValue(0) && dz.remove(c) == false)
							return false;
						continue;
					}
					if (rzx[c] != -1 && dx.contains(rzx[c]) && dy.contains(rzy[c]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va == 0) // because it involves vc=0, and vc = 0 already handled (and we need to be careful
										// about division by zero
							continue;
						int vb = vc / va;
						if (va > 0 && vc > 0 && va * dy.firstValue() > vc) // TODO other ways of breaking?
							break;
						if (vc % va == 0 && dy.containsValue(vb)) {
							rzx[c] = a;
							rzy[c] = dy.toIdx(vb);
							continue extern;
						}
					}
					if (dz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x / y <op> z
	// ************************************************************************

	public static abstract class Div3 extends Primitive3 implements TagNotCallCompleteFiltering {

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case EQ:
				return new Div3EQ(pb, x, y, z);
			default:
				throw new AssertionError("not implemented");
			}
		}

		public Div3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class Div3EQ extends Div3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] / t[1] == t[2];
			}

			public Div3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.size() * dy.size() > 200) { // hard coding // TODO what about AC Guaranteed?
					if (dz.removeValuesLT(dx.firstValue() / dy.lastValue()) == false || dz.removeValuesGT(dx.lastValue() / dy.firstValue()) == false)
						return false;
					return AC.enforceDivGE(dx, dy, dz.firstValue()) && AC.enforceDivLE(dx, dy, dz.lastValue());
				}

				if (dx.firstValue() >= dy.lastValue() && dz.removeValueIfPresent(0) == false)
					return false;
				boolean zero = dz.containsValue(0);
				if (!zero || dx.lastValue() >= dy.lastValue())
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va == 0) {
							if (!zero && dx.remove(a) == false)
								return false;
							continue;
						}
						if (zero && va < dy.lastValue())
							continue;
						if (dy.contains(rx[a]) && dz.containsValue(va / dy.toVal(rx[a])))
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va / dy.toVal(b);
							if (vc < dz.firstValue())
								break;
							if (dz.containsValue(vc)) {
								rx[a] = b;
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
				if (!zero || !dx.containsValue(0))
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (zero && dx.firstValue() < vb)
							break; // all remaining values are supported
						if (dx.contains(ry[b]) && dz.containsValue(dx.toVal(ry[b]) / vb))
							continue;
						for (int a = dx.last(); a != -1; a = dx.prev(a)) {
							int va = dx.toVal(a);
							if (va < vb) {
								assert !zero;
								break;
							}
							if (dz.containsValue(va / vb)) {
								ry[b] = a;
								continue extern;
							}
						}
						if (dy.remove(b) == false)
							return false;
					}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (vc == 0) {
						assert dx.firstValue() < dy.lastValue();
						continue; // already treated at the beginning of the method
					}
					if (rzx[c] != -1 && dx.contains(rzx[c]) && dy.contains(rzy[c]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va / dy.lastValue() > vc)
							break;
						if (va / dy.firstValue() < vc)
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int res = va / dy.toVal(b);
							if (res < vc)
								break;
							if (res == vc) {
								rzx[c] = a;
								rzy[c] = b;
								continue extern;
							}
						}
					}
					if (dz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x % y <op> z
	// ************************************************************************

	public static abstract class Mod3 extends Primitive3 {

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case EQ:
				return new Mod3EQ(pb, x, y, z);
			default:
				throw new AssertionError("not implemented");
			}
		}

		public Mod3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class Mod3EQ extends Mod3 {

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return t[0] % t[1] == t[2];
			}

			public Mod3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				if (dy.containsValue(0)) {
					control(dy.size() > 1);
					dy.removeValueAtConstructionTime(0);
				}
				control(dx.firstValue() >= 0 && dy.firstValue() > 0 && dz.firstValue() >= 0);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (va < dy.lastValue() && dz.containsValue(va)) // remainder is necessarily va because va < vb
						continue;
					if (dy.contains(rx[a]) && dz.containsValue(va % dy.toVal(rx[a])))
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (va < vb) // means that the remainder with remaining values of y lead to va (and this has
										// been considered earlier)
							break;
						if (dz.containsValue(va % vb)) {
							rx[a] = b;
							continue extern;
						}
					}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (vb <= dz.firstValue()) {
						if (dy.remove(b) == false)
							return false;
						continue;
					}
					if (dx.contains(ry[b]) && dz.containsValue(dx.toVal(ry[b]) % vb))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int vc = dx.toVal(a) % vb;
						if (dz.containsValue(vc)) {
							ry[b] = a;
							continue extern;
						}
					}
					if (dy.remove(b) == false)
						return false;
				}
				if (dz.removeValuesGE(dy.lastValue()) == false) // because remainder is less than the denominator
					return false;
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (rzx[c] != -1 && dx.contains(rzx[c]) && dy.contains(rzy[c]))
						continue;
					for (int b = dy.last(); b != -1; b = dy.prev(b)) {
						int vb = dy.toVal(b);
						if (vb <= vc)
							break;
						int nMultiples = dx.lastValue() / vb;
						if (dx.size() <= nMultiples) {
							for (int a = dx.first(); a != -1; a = dx.next(a)) {
								if (dx.toVal(a) % vb == vc) {
									rzx[c] = a;
									rzy[c] = b;
									continue extern;
								}
							}
						} else {
							int multiple = vc;
							while (true) {
								if (multiple > dx.lastValue())
									break;
								if (dx.containsValue(multiple)) {
									rzx[c] = dx.toIdx(multiple);
									rzy[c] = b;
									continue extern;
								}
								multiple += vb;
							}
						}
					}
					if (dz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for |x - y| <op> z
	// ************************************************************************

	public static abstract class Dist3 extends Primitive3 {

		public static Constraint buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case EQ:
				return new Dist3EQ(pb, x, y, z);
			default:
				return null; // to be able to post it differently, rather than throw new AssertionError
			}
		}

		public Dist3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		// time java ac GolombRuler-10.xml -varh=Dom => same search tree with CT, Intension and DistEQ3
		public static final class Dist3EQ extends Dist3 {

			boolean multidirectional = true; // hard coding

			@Override
			public boolean isSatisfiedBy(int[] t) {
				return Math.abs(t[0] - t[1]) == t[2];
			}

			public Dist3EQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
			}

			private boolean supportx(Domain d, int v, int a, int b, int c) {
				if (d.containsValue(v)) {
					rx[a] = b;
					if (multidirectional) {
						ry[b] = a;
						rzx[c] = a;
						rzy[c] = b;
					}
					return true;
				}
				return false;
			}

			private boolean supporty(Domain d, int v, int a, int b, int c) {
				if (d.containsValue(v)) {
					ry[b] = a;
					if (multidirectional) {
						rzx[c] = a;
						rzy[c] = b;
					}
					return true;
				}
				return false;
			}

			private boolean supportz(Domain d, int v, int a, int b, int c) {
				if (d.containsValue(v)) {
					rzx[c] = a;
					rzy[c] = b;
					return true;
				}
				return false;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (dy.contains(rx[a]) && dz.containsValue(Math.abs(va - dy.toVal(rx[a]))))
						continue;
					if (dy.size() <= dz.size())
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = Math.abs(va - dy.toVal(b));
							if (supportx(dz, vc, a, b, dz.toIdx(vc)))
								continue extern;
						}
					else
						for (int c = dz.first(); c != -1; c = dz.next(c)) {
							int vb = va - dz.toVal(c);
							if (supportx(dy, vb, a, dy.toIdx(vb), c))
								continue extern;
							vb = va + dz.toVal(c);
							if (supportx(dy, vb, a, dy.toIdx(vb), c))
								continue extern;
						}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (dx.contains(ry[b]) && dz.containsValue(Math.abs(vb - dx.toVal(ry[b]))))
						continue;
					if (dx.size() <= dz.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = Math.abs(vb - dx.toVal(a));
							if (supporty(dz, vc, a, b, dz.toIdx(vc)))
								continue extern;
						}
					else
						for (int c = dz.first(); c != -1; c = dz.next(c)) {
							int va = vb - dz.toVal(c);
							if (supporty(dx, va, dx.toIdx(va), b, c))
								continue extern;
							va = vb + dz.toVal(c);
							if (supporty(dx, va, dx.toIdx(va), b, c))
								continue extern;
						}
					if (dy.remove(b) == false)
						return false;
				}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (rzx[c] != -1 && dx.contains(rzx[c]) && dy.contains(rzy[c]))
						continue;
					if (dx.size() <= dy.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vb = dx.toVal(a) - vc;
							if (supportz(dy, vb, a, dy.toIdx(vb), c))
								continue extern;
							vb = dx.toVal(a) + vc;
							if (supportz(dy, vb, a, dy.toIdx(vb), c))
								continue extern;
						}
					else
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int va = dy.toVal(b) - vc;
							if (supportz(dx, va, dx.toIdx(va), b, c))
								continue extern;
							va = dy.toVal(b) + vc;
							if (supportz(dx, va, dx.toIdx(va), b, c))
								continue extern;
						}
					if (dz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Class for ift(x,y,z)
	// ************************************************************************

	public static class IFT3 extends Primitive3 {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			return t[0] == 1 ? (t[1] == 1) : (t[2] == 1);
		}

		public IFT3(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
			control(dx.is01() && dy.is01() && dz.is01());
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			if (dx.size() == 2) {
				if (!dy.contains(1))
					return dx.remove(1) && dz.removeIfPresent(0) && entail();
				if (!dz.contains(1))
					return dx.remove(0) && dy.removeIfPresent(0) && entail();
			} else if (!dx.contains(0))
				return dy.removeIfPresent(0) && entail();
			else // only 0 in dx
				return dz.removeIfPresent(0) && entail();
			return true;
		}
	}

}
