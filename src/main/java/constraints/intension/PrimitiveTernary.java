/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.intension;

import static constraints.intension.PrimitiveBinary.enforceEQ;
import static constraints.intension.PrimitiveBinary.enforceGE;
import static constraints.intension.PrimitiveBinary.enforceGT;
import static constraints.intension.PrimitiveBinary.enforceLE;
import static constraints.intension.PrimitiveBinary.enforceLT;
import static constraints.intension.PrimitiveBinary.enforceNE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;

import java.math.BigInteger;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.global.SumWeighted;
import interfaces.Tags.TagFilteringCompleteAtEachCall;
import interfaces.Tags.TagGACGuaranteed;
import interfaces.Tags.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class PrimitiveTernary extends Primitive implements TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagUnsymmetric {

	protected final Variable x, y, z;

	protected Domain dx, dy, dz;

	int[] rx, ry, rzx, rzy; // residues for values in the domains of x, y and z

	public PrimitiveTernary(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, pb.api.vars(x, y, z));
		this.x = x;
		this.y = y;
		this.z = z;
		this.dx = x.dom;
		this.dy = y.dom;
		this.dz = z.dom;
	}

	protected void buildThreeResidueStructure() {
		this.rx = new int[dx.initSize()];
		this.ry = new int[dy.initSize()];
		this.rzx = new int[dz.initSize()];
	}

	protected void buildFourResidueStructure() {
		this.rx = new int[dx.initSize()];
		this.ry = new int[dy.initSize()];
		this.rzx = Kit.repeat(-1, dz.initSize());
		this.rzy = Kit.repeat(-1, dz.initSize());
	}

	// ************************************************************************
	// ***** Classes for x + y <op> z (CtrPrimitiveTernaryAdd)
	// ************************************************************************

	public static abstract class PrimitiveTernaryAdd extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == EQ)
				return pb.addCtr(new AddEQ3(pb, x, y, z));
			return pb.addCtr(SumWeighted.buildFrom(pb, pb.api.vars(z, x, y), pb.api.vals(-1, 1, 1), op, 0)); // we order variables according to coeffs
		}

		public PrimitiveTernaryAdd(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class AddEQ3 extends PrimitiveTernaryAdd {

			boolean multidirectional = false; // hard coding

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == t[2];
			}

			public AddEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildThreeResidueStructure();
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (dy.isPresent(rx[a]) && dz.isPresentValue(va + dy.toVal(rx[a])))
						continue;
					if (dy.size() <= dz.size())
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va + dy.toVal(b);
							if (vc > dz.lastValue())
								break;
							if (dz.isPresentValue(vc)) {
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
							if (dy.isPresentValue(vb)) {
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
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (dx.isPresent(ry[b]) && dz.isPresentValue(vb + dx.toVal(ry[b])))
						continue;
					if (dx.size() <= dz.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = vb + dx.toVal(a);
							if (vc > dz.lastValue())
								break;
							if (dz.isPresentValue(vc)) {
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
							if (dx.isPresentValue(va)) {
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
					if (dx.isPresent(rzx[c]) && dy.isPresentValue(vc - dx.toVal(rzx[c])))
						continue;
					if (dx.size() <= dy.size())
						for (int a = dx.last(); a != -1; a = dx.prev(a)) {
							int vb = vc - dx.toVal(a);
							if (vb > dy.lastValue())
								break;
							if (dy.isPresentValue(vb)) {
								rzx[c] = a;
								continue extern;
							}
						}
					else
						for (int b = dy.last(); b != -1; b = dy.prev(b)) {
							int va = vc - dy.toVal(b);
							if (va > dx.lastValue())
								break;
							if (dx.isPresentValue(va)) {
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
	// ***** Classes for x - y <op> z (CtrPrimitiveTernarySub)
	// ************************************************************************

	public static abstract class PrimitiveTernarySub extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			return PrimitiveTernaryAdd.buildFrom(pb, y, z, op, x); // x - y <op> z is equivalent to y + z <op> x
		}

		public PrimitiveTernarySub(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> z (CtrPrimitiveTernaryMul)
	// ************************************************************************

	public static abstract class PrimitiveTernaryMul extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(x.dom.is01() ? new MulEQ3b(pb, x, y, z) : y.dom.is01() ? new MulEQ3b(pb, y, x, z) : new MulEQ3(pb, y, x, z));
			throw new UnsupportedOperationException();
		}

		public PrimitiveTernaryMul(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class MulEQ3b extends PrimitiveTernaryMul {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public MulEQ3b(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				control(dx.is01(), "The first variable should be of type 01");
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0 || dy.onlyContainsValue(0)) // only 0 remaining in dx or dy => z must be 0
					return dz.reduceToValue(0);
				if (dz.onlyContainsValue(0)) { // only 0 remaining in dz
					if (dx.first() == 0 && dy.isPresentValue(0)) // if 0 in the domains of x and y, every value is supported
						return true;
					return dx.first() == 0 ? dx.reduceTo(0) : dy.reduceToValue(0); // if 0 not in dy => x must be 0, else => y must be 0
				}
				if (dz.isPresentValue(0)) {
					if (dx.first() == 1 && !dy.isPresentValue(0) && dz.removeValue(0) == false)
						return false;
				} else if (dx.removeIfPresent(0) == false || dy.removeValueIfPresent(0) == false)
					return false;

				if (dx.first() == 1) // only 1 remaining in dx => y = z
					return PrimitiveBinary.enforceEQ(dy, dz);

				assert dx.size() == 2 && dz.isPresentValue(0) && dz.size() > 1; // because if 0 not in z, dx.size() cannot be 2
				// every value of dy is supported (by both 0 in x and z); we still need to filter z (and possibly 1 out of dx)

				int sizeBefore = dz.size();
				for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (vc != 0 && !dy.isPresentValue(vc))
						dz.removeElementary(c);
				}
				dz.afterElementaryCalls(sizeBefore);
				if (dz.size() == 1) {
					assert dz.onlyContainsValue(0);
					dx.removeSafely(1);
				}
				return true;
			}
		}

		public static final class MulEQ3 extends PrimitiveTernaryMul {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public MulEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				Kit.control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
				Kit.control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (!dy.isPresentValue(0) || !dz.isPresentValue(0)) // if 0 is present in dy and dz, all values of x are supported
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va == 0) {
							if (!dz.isPresentValue(0) && dx.remove(a) == false)
								return false;
							continue;
						}
						if (dy.isPresent(rx[a]) && dz.isPresentValue(va * dy.toVal(rx[a])))
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va * dy.toVal(b);
							if ((va > 0 && vc > dz.lastValue()) || (va < 0 && vc < dz.firstValue()))
								break;
							if (dz.isPresentValue(vc)) {
								rx[a] = b;
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
				if (!dx.isPresentValue(0) || !dz.isPresentValue(0)) // if 0 is present in dx and dz, all values of y are supported
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (vb == 0) {
							if (!dz.isPresentValue(0) && dy.remove(b) == false)
								return false;
							continue;
						}
						if (dx.isPresent(ry[b]) && dz.isPresentValue(vb * dx.toVal(ry[b])))
							continue;
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = vb * dx.toVal(a);
							if ((vb > 0 && vc > dz.lastValue()) || (vb < 0 && vc < dz.firstValue()))
								break;
							if (dz.isPresentValue(vc)) {
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
						if (!dx.isPresentValue(0) && !dy.isPresentValue(0) && dz.remove(c) == false)
							return false;
						continue;
					}
					if (rzx[c] != -1 && dx.isPresent(rzx[c]) && dy.isPresent(rzy[c]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						int vb = vc / va;
						if (va > 0 && vc > 0 && (va > vc / 2 || va * dy.firstValue() > vc)) // TODO correct. right? other ways of breaking?
							break;
						if (vc % va == 0 && dy.isPresentValue(vb)) {
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
	// ***** Classes for x / y <op> z (CtrPrimitiveTernaryDiv)
	// ************************************************************************

	public static abstract class PrimitiveTernaryDiv extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new DivEQ3(pb, x, y, z));
			throw new UnsupportedOperationException();
		}

		public PrimitiveTernaryDiv(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class DivEQ3 extends PrimitiveTernaryDiv {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] / t[1] == t[2];
			}

			public DivEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.firstValue() >= dy.lastValue() && dz.removeValueIfPresent(0) == false)
					return false;
				boolean zero = dz.isPresentValue(0);
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
						if (dy.isPresent(rx[a]) && dz.isPresentValue(va / dy.toVal(rx[a])))
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va / dy.toVal(b);
							if (vc < dz.firstValue())
								break;
							if (dz.isPresentValue(vc)) {
								rx[a] = b;
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
				if (!zero || !dx.isPresentValue(0))
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (zero && dx.firstValue() < vb)
							break; // all remaining values are supported
						if (dx.isPresent(ry[b]) && dz.isPresentValue(dx.toVal(ry[b]) / vb))
							continue;
						for (int a = dx.last(); a != -1; a = dx.prev(a)) {
							int va = dx.toVal(a);
							if (va < vb) {
								assert !zero;
								break;
							}
							if (dz.isPresentValue(va / vb)) {
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
					if (rzx[c] != -1 && dx.isPresent(rzx[c]) && dy.isPresent(rzy[c]))
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
	// ***** Classes for x % y <op> z (CtrPrimitiveTernaryMod)
	// ************************************************************************

	public static abstract class PrimitiveTernaryMod extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new ModEQ3(pb, x, y, z));
			throw new UnsupportedOperationException();
		}

		public PrimitiveTernaryMod(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class ModEQ3 extends PrimitiveTernaryMod {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] % t[1] == t[2];
			}

			public ModEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
				control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (va < dy.lastValue() && dz.isPresentValue(va)) // remainder is necessarily va because va < vb
						continue;
					if (dy.isPresent(rx[a]) && dz.isPresentValue(va % dy.toVal(rx[a])))
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (va < vb) // means that the remainder with remaining values of y lead to va (and this has been considered earlier)
							break;
						if (dz.isPresentValue(va % vb)) {
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
					if (dx.isPresent(ry[b]) && dz.isPresentValue(dx.toVal(ry[b]) % vb))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int vc = dx.toVal(a) % vb;
						if (dz.isPresentValue(vc)) {
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
					if (rzx[c] != -1 && dx.isPresent(rzx[c]) && dy.isPresent(rzy[c]))
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
								if (dx.isPresentValue(multiple)) {
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
	// ***** Classes for |x - y| <op> z (CtrPrimitiveTernaryDist)
	// ************************************************************************

	public static abstract class PrimitiveTernaryDist extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == EQ)
				return pb.addCtr(new DistEQ3(pb, x, y, z));
			throw new UnsupportedOperationException();
		}

		public PrimitiveTernaryDist(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		// time java ac GolombRuler-10.xml -varh=Dom => same search tree with CT, Intension and DistEQ3
		public static final class DistEQ3 extends PrimitiveTernaryDist {

			boolean multidirectional = true; // hard coding

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) == t[2];
			}

			public DistEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				buildFourResidueStructure();
			}

			private boolean supportx(Domain d, int v, int a, int b, int c) {
				if (d.isPresentValue(v)) {
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
				if (d.isPresentValue(v)) {
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
				if (d.isPresentValue(v)) {
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
					if (dy.isPresent(rx[a]) && dz.isPresentValue(Math.abs(va - dy.toVal(rx[a]))))
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
					if (dx.isPresent(ry[b]) && dz.isPresentValue(Math.abs(vb - dx.toVal(ry[b]))))
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
					if (rzx[c] != -1 && dx.isPresent(rzx[c]) && dy.isPresentValue(rzy[c]))
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
	// ***** Classes for x = (y <op> z) (CtrPrimitiveTernaryLog)
	// ************************************************************************

	public static abstract class PrimitiveTernaryLog extends PrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			switch (op) {
			case LT:
				return pb.addCtr(new LogLT3(pb, x, y, z));
			case LE:
				return pb.addCtr(new LogLE3(pb, x, y, z));
			case GE:
				return pb.addCtr(new LogGE3(pb, x, y, z));
			case GT:
				return pb.addCtr(new LogGT3(pb, x, y, z));
			case EQ:
				return pb.addCtr(new LogEQ3(pb, x, y, z));
			case NE:
				return pb.addCtr(new LogNE3(pb, x, y, z));
			}
			throw new AssertionError();
		}

		public PrimitiveTernaryLog(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
			control(dx.is01(), "The first variable should be of type 01");
		}

		public static final class LogLT3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] < t[2]);
			}

			public LogLT3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.lastValue() < dz.firstValue() && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.firstValue() >= dz.lastValue() && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && enforceLT(dy, dz) == false) // because only 1 remaining implies y < z
					return false;
				if (dx.last() == 0 && enforceGE(dy, dz) == false) // because only 0 remaining implies y >= z
					return false;
				return true;
			}
		}

		public static final class LogLE3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] <= t[2]);
			}

			public LogLE3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.lastValue() <= dz.firstValue() && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.firstValue() > dz.lastValue() && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && enforceLE(dy, dz) == false) // because only 1 remaining implies y <= z
					return false;
				if (dx.last() == 0 && enforceGT(dy, dz) == false) // because only 0 remaining implies y > z
					return false;
				return true;
			}
		}

		public static final class LogGE3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] >= t[2]);
			}

			public LogGE3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.firstValue() >= dz.lastValue() && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.lastValue() < dz.firstValue() && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && enforceGE(dy, dz) == false) // because only 1 remaining implies y >= z
					return false;
				if (dx.last() == 0 && enforceLT(dy, dz) == false) // because only 0 remaining implies y < z
					return false;
				return true;
			}
		}

		public static final class LogGT3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] > t[2]);
			}

			public LogGT3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.first() == 0 && dy.firstValue() > dz.lastValue() && dx.remove(0) == false)
					return false;
				if (dx.last() == 1 && dy.lastValue() <= dz.firstValue() && dx.remove(1) == false)
					return false;
				if (dx.first() == 1 && enforceGT(dy, dz) == false) // because only 1 remaining implies y > z
					return false;
				if (dx.last() == 0 && enforceLE(dy, dz) == false) // because only 0 remaining implies y <= z
					return false;
				return true;
			}
		}

		public static final class LogEQ3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] == t[2]);
			}

			private int residue; // for a common value in the domains of y and z, supporting (x,1)

			public LogEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.removeIfPresent(dy.firstValue() == dz.firstValue() ? 0 : 1); // remember that indexes and values match for x
				if (dx.first() == 1 && enforceEQ(dy, dz) == false) // because only 1 remaining implies y = z
					return false;
				if (dx.last() == 0 && enforceNE(dy, dz) == false) // because only 0 remaining implies y != z
					return false;
				assert dx.size() == 2;
				// we know that 0 for x is supported because the domain of y or z is not singleton
				if (dy.isPresentValue(residue) && dz.isPresentValue(residue))
					return true;
				// we look for a support for (x,1), and record it as a residue
				int v = dy.size() <= dz.size() ? dy.firstCommonValueWith(dz) : dz.firstCommonValueWith(dy); // commonValueIn(dy, dz);
				if (v != Integer.MAX_VALUE)
					residue = v;
				else
					dx.removeSafely(1);
				return true;
			}
		}

		public static final class LogNE3 extends PrimitiveTernaryLog {

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] != t[2]);
			}

			int residue; // for a common value in the domains of y and z, supporting (x,0)

			public LogNE3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.removeIfPresent(dy.firstValue() != dz.firstValue() ? 0 : 1); // remember that indexes and values match for x
				if (dx.first() == 1 && enforceNE(dy, dz) == false) // because only 1 remaining implies y != z
					return false;
				if (dx.last() == 0 && enforceEQ(dy, dz) == false) // because only 0 remaining implies y = z
					return false;
				assert dx.size() == 2;
				// we know that (x,1) is supported because the domain of y and/or the domain of z is not singleton
				if (dy.isPresentValue(residue) && dz.isPresentValue(residue))
					return true;
				// we look for a support for (x,0), and record it as a residue
				int v = dy.size() <= dz.size() ? dy.firstCommonValueWith(dz) : dz.firstCommonValueWith(dy); // commonValueIn(dy, dz);
				if (v != Integer.MAX_VALUE)
					residue = v;
				else
					dx.removeSafely(0);
				return true;
			}
		}
	}
}
