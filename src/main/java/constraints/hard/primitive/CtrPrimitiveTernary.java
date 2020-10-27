/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import static constraints.hard.primitive.CtrPrimitiveBinary.enforceEQ;
import static constraints.hard.primitive.CtrPrimitiveBinary.enforceGE;
import static constraints.hard.primitive.CtrPrimitiveBinary.enforceGT;
import static constraints.hard.primitive.CtrPrimitiveBinary.enforceLE;
import static constraints.hard.primitive.CtrPrimitiveBinary.enforceLT;
import static constraints.hard.primitive.CtrPrimitiveBinary.enforceNE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;

import java.math.BigInteger;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.hard.global.SumWeighted;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import utility.exceptions.MissingImplementationException;
import utility.exceptions.UnreachableCodeException;
import variables.Variable;
import variables.domains.Domain;

public abstract class CtrPrimitiveTernary extends CtrPrimitive implements TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagUnsymmetric {

	protected final Variable x, y, z;

	protected Domain dx, dy, dz;

	public CtrPrimitiveTernary(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, pb.api.vars(x, y, z));
		this.x = x;
		this.y = y;
		this.z = z;
		this.dx = x.dom;
		this.dy = y.dom;
		this.dz = z.dom;
	}

	// ************************************************************************
	// ***** Classes for x + y <op> z (CtrPrimitiveTernaryAdd)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryAdd extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == EQ)
				return pb.addCtr(new AddEQ3(pb, x, y, z));
			return pb.addCtr(SumWeighted.buildFrom(pb, pb.api.vars(x, y, z), pb.api.vals(1, 1, -1), op, 0));
		}

		public CtrPrimitiveTernaryAdd(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class AddEQ3 extends CtrPrimitiveTernaryAdd {

			int[] resx, resy, resz; // residues for values in the domains of x, y and z

			boolean multidirectional = false; // hard coding

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == t[2];
			}

			public AddEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				this.resx = new int[dx.initSize()];
				this.resy = new int[dy.initSize()];
				this.resz = new int[dz.initSize()];
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (dy.isPresent(resx[a]) && dz.isPresentValue(va + dy.toVal(resx[a])))
						continue;
					if (dy.size() <= dz.size())
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va + dy.toVal(b);
							if (vc > dz.lastValue())
								break;
							if (dz.isPresentValue(vc)) {
								resx[a] = b;
								if (multidirectional) {
									resy[b] = a;
									resz[dz.toIdx(vc)] = a;
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
								resx[a] = dy.toIdx(vb);
								if (multidirectional) {
									resy[dy.toIdx(vb)] = a;
									resz[c] = a;
								}
								continue extern;
							}
						}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (dx.isPresent(resy[b]) && dz.isPresentValue(vb + dx.toVal(resy[b])))
						continue;
					if (dx.size() <= dz.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = vb + dx.toVal(a);
							if (vc > dz.lastValue())
								break;
							if (dz.isPresentValue(vc)) {
								resy[b] = a;
								if (multidirectional)
									resz[dz.toIdx(vc)] = a;
								continue extern;
							}
						}
					else
						for (int c = dz.first(); c != -1; c = dz.next(c)) {
							int va = dz.toVal(c) - vb;
							if (va > dx.lastValue())
								break;
							if (dx.isPresentValue(va)) {
								resy[b] = dx.toIdx(va);
								if (multidirectional)
									resz[c] = dx.toIdx(va);
								continue extern;
							}
						}
					if (dy.remove(b) == false)
						return false;
				}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (dx.isPresent(resz[c]) && dy.isPresentValue(vc - dx.toVal(resz[c])))
						continue;
					if (dx.size() <= dy.size())
						for (int a = dx.last(); a != -1; a = dx.prev(a)) {
							int vb = vc - dx.toVal(a);
							if (vb > dy.lastValue())
								break;
							if (dy.isPresentValue(vb)) {
								resz[c] = a;
								continue extern;
							}
						}
					else
						for (int b = dy.last(); b != -1; b = dy.prev(b)) {
							int va = vc - dy.toVal(b);
							if (va > dx.lastValue())
								break;
							if (dx.isPresentValue(va)) {
								resz[c] = dx.toIdx(va);
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

	public static abstract class CtrPrimitiveTernarySub extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			return CtrPrimitiveTernaryAdd.buildFrom(pb, y, z, op, x); // x - y <op> z is equivalent to y + z <op> x
		}

		public CtrPrimitiveTernarySub(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}
	}

	// ************************************************************************
	// ***** Classes for x * y <op> z (CtrPrimitiveTernaryMul)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryMul extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ) {
				if (x.dom.is01())
					return pb.addCtr(new MulEQ3b(pb, x, y, z));
				if (y.dom.is01())
					return pb.addCtr(new MulEQ3b(pb, y, x, z));
				return pb.addCtr(new MulEQ3(pb, y, x, z));
			}
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryMul(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class MulEQ3b extends CtrPrimitiveTernaryMul {

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public MulEQ3b(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				Utilities.control(dx.is01(), "The first variable should be of type 01");
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dx.last() == 0) // only 0 remaining in dx => z must be 0
					return dz.reduceToValue(0);
				if (dy.onlyContainsValue(0)) // only 0 remaining in dy => z must be 0
					return dz.reduceToValue(0);
				if (dz.onlyContainsValue(0)) { // only 0 remaining in dz
					if (dx.first() == 0 && dy.isPresentValue(0)) // if 0 in the domains of x and y, every value is supported
						return true;
					if (dx.first() == 0)
						return dx.reduceTo(0);
					if (dy.isPresentValue(0))
						return dy.reduceToValue(0);
					return dz.fail();
				}
				if (dz.isPresentValue(0)) {
					if (dx.first() == 1 && !dy.isPresentValue(0) && dz.removeValue(0) == false)
						return false;
				} else {
					if (dx.removeIfPresent(0) == false)
						return false;
					if (dy.removeValueIfPresent(0) == false)
						return false;
				}
				if (dx.first() == 1) { // only 1 remaining in dx => y = z
					if (dy.removeValuesNotIn(dz) == false)
						return false;
					assert dy.size() <= dz.size();
					if (dy.size() == dz.size())
						return true;
					boolean consistent = dz.removeValuesNotIn(dy);
					assert consistent;
					return true;
				}
				assert dx.size() == 2 && dz.isPresentValue(0) && dz.size() > 1;
				// every value of dy is supported (by both 0 in x and z); we still need to filter z (and possibly 1 out of dx)
				// TODO using a residue here ?
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

		public static final class MulEQ3 extends CtrPrimitiveTernaryMul {

			int[] resx, resy, resz1, resz2; // residues for values in the domains of x, y and z

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] * t[1] == t[2];
			}

			public MulEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				Kit.control(Utilities.isSafeInt(BigInteger.valueOf(dx.firstValue()).multiply(BigInteger.valueOf(dy.firstValue())).longValueExact()));
				Kit.control(Utilities.isSafeInt(BigInteger.valueOf(dx.lastValue()).multiply(BigInteger.valueOf(dy.lastValue())).longValueExact()));
				this.resx = new int[dx.initSize()];
				this.resy = new int[dy.initSize()];
				this.resz1 = Kit.repeat(-1, dz.initSize());
				this.resz2 = Kit.repeat(-1, dz.initSize());
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (!dy.isPresentValue(0) || !dz.isPresentValue(0))
					extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						if (va == 0) {
							if (!dz.isPresentValue(0) && dx.remove(a) == false)
								return false;
							continue;
						}
						if (dy.isPresent(resx[a]) && dz.isPresentValue(va * dy.toVal(resx[a])))
							continue;
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = va * dy.toVal(b);
							if ((va > 0 && vc > dz.lastValue()) || (va < 0 && vc < dz.firstValue()))
								break;
							if (dz.isPresentValue(vc)) {
								resx[a] = b;
								continue extern;
							}
						}
						if (dx.remove(a) == false)
							return false;
					}
				if (!dx.isPresentValue(0) || !dz.isPresentValue(0))
					extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (vb == 0) {
							if (!dz.isPresentValue(0) && dy.remove(b) == false)
								return false;
							continue;
						}
						if (dx.isPresent(resy[b]) && dz.isPresentValue(vb * dx.toVal(resy[b])))
							continue;
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = vb * dx.toVal(a);
							if ((vb > 0 && vc > dz.lastValue()) || (vb < 0 && vc < dz.firstValue()))
								break;
							if (dz.isPresentValue(vc)) {
								resy[b] = a;
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
					if (resz1[c] != -1 && dx.isPresent(resz1[c]) && dy.isPresent(resz2[c]))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int va = dx.toVal(a);
						int vb = vc / va;
						// if (va > 0 && vc > 0 && va > vc / 2) // TODO is that correct? other ways of breaking?
						// break;
						if (vc % va == 0 && dy.isPresentValue(vb)) {
							resz1[c] = a;
							resz2[c] = dy.toIdx(vb);
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
	// ***** Classes for x % y <op> z (CtrPrimitiveTernaryMod)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryMod extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new ModEQ3(pb, x, y, z));
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryMod(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class ModEQ3 extends CtrPrimitiveTernaryMod {

			int[] resx, resy, resz1, resz2; // residues for values in the domains of x, y and z

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] % t[1] == t[2];
			}

			public ModEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
				this.resx = new int[dx.initSize()];
				this.resy = new int[dy.initSize()];
				this.resz1 = Kit.repeat(-1, dz.initSize());
				this.resz2 = Kit.repeat(-1, dz.initSize());
			}

			@Override
			public Boolean isSymmetric() {
				return false;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (va < dy.lastValue() && dz.isPresentValue(va)) // remainder in z is then necessarily va
						continue;
					if (dy.isPresent(resx[a]) && dz.isPresentValue(va % dy.toVal(resx[a])))
						continue;
					for (int b = dy.first(); b != -1; b = dy.next(b)) {
						int vb = dy.toVal(b);
						if (va < vb) // means that the remainder with remaining values of y lead to va (and this has been considered earlier)
							break;
						if (dz.isPresentValue(va % vb)) {
							resx[a] = b;
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
					if (dx.isPresent(resy[b]) && dz.isPresentValue(dx.toVal(resy[b]) % vb))
						continue;
					for (int a = dx.first(); a != -1; a = dx.next(a)) {
						int vc = dx.toVal(a) % vb;
						if (dz.isPresentValue(vc)) {
							resy[b] = a;
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
					if (resz1[c] != -1 && dx.isPresent(resz1[c]) && dy.isPresent(resz2[c]))
						continue;
					for (int b = dy.last(); b != -1; b = dy.prev(b)) {
						int vb = dy.toVal(b);
						if (vb < vc)
							break;
						int nMultiples = dx.lastValue() / vb;
						if (dx.size() <= nMultiples) {
							for (int a = dx.first(); a != -1; a = dx.next(a)) {
								if (dx.toVal(a) % vb == vc) {
									resz1[c] = a;
									resz2[c] = b;
									continue extern;
								}
							}
						} else {
							int multiple = vc;
							while (true) {
								if (multiple > dx.lastValue())
									break;
								if (dx.isPresentValue(multiple)) {
									resz1[c] = dx.toIdx(multiple);
									resz2[c] = b;
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

	public static abstract class CtrPrimitiveTernaryDist extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == EQ)
				return pb.addCtr(new DistEQ3(pb, x, y, z));
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryDist(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		// time java ac GolombRuler-10.xml -varh=Dom => same search tree with CT, Intension and DistEQ3
		public static final class DistEQ3 extends CtrPrimitiveTernaryDist {

			int[] resx, resy, resz1, resz2; // residues for values in the domains of x, y and z

			boolean multidirectional = true; // hard coding

			@Override
			public final boolean checkValues(int[] t) {
				return Math.abs(t[0] - t[1]) == t[2];
			}

			public DistEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				this.resx = new int[dx.initSize()];
				this.resy = new int[dy.initSize()];
				this.resz1 = Kit.repeat(-1, dz.initSize());
				this.resz2 = Kit.repeat(-1, dz.initSize());
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = dx.first(); a != -1; a = dx.next(a)) {
					int va = dx.toVal(a);
					if (dy.isPresent(resx[a]) && dz.isPresentValue(Math.abs(va - dy.toVal(resx[a]))))
						continue;
					if (dy.size() <= dz.size())
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int vc = Math.abs(va - dy.toVal(b));
							if (dz.isPresentValue(vc)) {
								resx[a] = b;
								if (multidirectional) {
									resy[b] = a;
									resz1[dz.toIdx(vc)] = a;
									resz2[dz.toIdx(vc)] = b;
								}
								continue extern;
							}
						}
					else
						for (int c = dz.first(); c != -1; c = dz.next(c)) {
							int vb = va - dz.toVal(c);
							if (dy.isPresentValue(vb)) {
								resx[a] = dy.toIdx(vb);
								if (multidirectional) {
									resy[dy.toIdx(vb)] = a;
									resz1[c] = a;
									resz2[c] = dy.toIdx(vb);
								}
								continue extern;
							}
							vb = va + dz.toVal(c);
							if (dy.isPresentValue(vb)) {
								resx[a] = dy.toIdx(vb);
								if (multidirectional) {
									resy[dy.toIdx(vb)] = a;
									resz1[c] = a;
									resz2[c] = dy.toIdx(vb);
								}
								continue extern;
							}
						}
					if (dx.remove(a) == false)
						return false;
				}
				extern: for (int b = dy.first(); b != -1; b = dy.next(b)) {
					int vb = dy.toVal(b);
					if (dx.isPresent(resy[b]) && dz.isPresentValue(Math.abs(vb - dx.toVal(resy[b]))))
						continue;
					if (dx.size() <= dz.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vc = Math.abs(vb - dx.toVal(a));
							if (dz.isPresentValue(vc)) {
								resy[b] = a;
								if (multidirectional) {
									resz1[dz.toIdx(vc)] = a;
									resz2[dz.toIdx(vc)] = b;
								}
								continue extern;
							}
						}
					else
						for (int c = dz.first(); c != -1; c = dz.next(c)) {
							int va = vb - dz.toVal(c);
							if (dx.isPresentValue(va)) {
								resy[b] = dx.toIdx(va);
								if (multidirectional) {
									resz1[c] = dx.toIdx(va);
									resz2[c] = b;

								}
								continue extern;
							}
							va = vb + dz.toVal(c);
							if (dx.isPresentValue(va)) {
								resy[b] = dx.toIdx(va);
								if (multidirectional) {
									resz1[c] = dx.toIdx(va);
									resz2[c] = b;
								}
								continue extern;
							}
						}
					if (dy.remove(b) == false)
						return false;
				}
				extern: for (int c = dz.first(); c != -1; c = dz.next(c)) {
					int vc = dz.toVal(c);
					if (resz1[c] != -1 && dx.isPresent(resz1[c]) && dy.isPresentValue(resz2[c]))
						continue;
					if (dx.size() <= dy.size())
						for (int a = dx.first(); a != -1; a = dx.next(a)) {
							int vb = dx.toVal(a) - vc;
							if (dy.isPresentValue(vb)) {
								resz1[c] = a;
								resz2[c] = dy.toIdx(vb);
								continue extern;
							}
							vb = dx.toVal(a) + vc;
							if (dy.isPresentValue(vb)) {
								resz1[c] = a;
								resz2[c] = dy.toIdx(vb);
								continue extern;
							}
						}
					else
						for (int b = dy.first(); b != -1; b = dy.next(b)) {
							int va = dy.toVal(b) - vc;
							if (dx.isPresentValue(va)) {
								resz1[c] = dx.toIdx(va);
								resz2[c] = b;
								continue extern;
							}
							va = dy.toVal(b) + vc;
							if (dx.isPresentValue(va)) {
								resz1[c] = dx.toIdx(va);
								resz2[c] = b;
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
	// ***** Classes for x = (y <op> z) (CtrPrimitiveTernaryLog)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryLog extends CtrPrimitiveTernary {

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
			throw new UnreachableCodeException();
		}

		public CtrPrimitiveTernaryLog(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
			Utilities.control(dx.is01(), "The first variable should be of type 01");
		}

		public static final class LogLT3 extends CtrPrimitiveTernaryLog {

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
				if (dx.first() == 1 && enforceLT(dy, dz) == false)
					return false; // because only 1 remaining implies y < z
				if (dx.last() == 0 && enforceGE(dy, dz) == false)
					return false; // because only 0 remaining implies y >= z
				return true;
			}
		}

		public static final class LogLE3 extends CtrPrimitiveTernaryLog {

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
				if (dx.first() == 1 && enforceLE(dy, dz) == false)
					return false; // because only 1 remaining implies y <= z
				if (dx.last() == 0 && enforceGT(dy, dz) == false)
					return false; // because only 0 remaining implies y > z
				return true;
			}
		}

		public static final class LogGE3 extends CtrPrimitiveTernaryLog {

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
				if (dx.first() == 1 && enforceGE(dy, dz) == false)
					return false; // because only 1 remaining implies y >= z
				if (dx.last() == 0 && enforceLT(dy, dz) == false)
					return false; // because only 0 remaining implies y < z
				return true;
			}
		}

		public static final class LogGT3 extends CtrPrimitiveTernaryLog {

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
				if (dx.first() == 1 && enforceGT(dy, dz) == false)
					return false; // because only 1 remaining implies y > z
				if (dx.last() == 0 && enforceLE(dy, dz) == false)
					return false; // because only 0 remaining implies y <= z
				return true;
			}
		}

		public static final class LogEQ3 extends CtrPrimitiveTernaryLog {

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

		public static final class LogNE3 extends CtrPrimitiveTernaryLog {

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
