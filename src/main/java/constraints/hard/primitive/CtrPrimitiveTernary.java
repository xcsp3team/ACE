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

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.hard.global.SumWeighted;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import interfaces.TagUnsymmetric;
import problem.Problem;
import utility.Kit;
import utility.exceptions.MissingImplementationException;
import variables.Variable;
import variables.domains.Domain;

public abstract class CtrPrimitiveTernary extends CtrPrimitive implements TagUnsymmetric { // implements TagGuaranteedGAC

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

		public static final class AddEQ3 extends CtrPrimitiveTernaryAdd implements TagGACGuaranteed {

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
					// System.out.println("dy " + dy.size() + " vs dz = " + dz.size());
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
	// ***** Classes for x * y <op> z (CtrPrimitiveTernaryMul)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryMul extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ) {
				if (x.dom.is01())
					return pb.addCtr(new MulEQ3b(pb, x, y, z));
				if (y.dom.is01())
					return pb.addCtr(new MulEQ3b(pb, y, x, z));
				throw new MissingImplementationException();
				// return null; // pb.addCtr(new MulEQ3(pb, x, y, z));
			}
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryMul(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class MulEQ3b extends CtrPrimitiveTernaryMul implements TagGACGuaranteed {

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
				if (dy.hasUniqueValue(0)) // only 0 remaining in dy => z must be 0
					return dz.reduceToValue(0);
				if (dz.hasUniqueValue(0)) { // only 0 remaining in dz
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
					if (dx.first() == 0 && dx.remove(0) == false)
						return false;
					if (dy.isPresentValue(0) && dy.removeValue(0) == false)
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
					assert dz.hasUniqueValue(0);
					dx.removeSafely(1);
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

		public static final class ModEQ3 extends CtrPrimitiveTernaryMod implements TagGACGuaranteed {

			int[] resx, resy, resz1, resz2; // residues for values in the domains of x, y and z

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] % t[1] == t[2];
			}

			public ModEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				Kit.control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
				this.resx = Kit.repeat(-1, dx.initSize());
				this.resy = Kit.repeat(-1, dy.initSize());
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
					if (resx[a] != -1 && dy.isPresent(resx[a]) && dz.isPresentValue(va % dy.toVal(resx[a])))
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
					if (resy[b] != -1 && dx.isPresent(resy[b]) && dz.isPresentValue(dx.toVal(resy[b]) % vb))
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
				if (dz.removeValues(TypeOperatorRel.GE, dy.lastValue()) == false) // because remainder is less than the denominator
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

		public static final class DistEQ3 extends CtrPrimitiveTernaryDist implements TagGACGuaranteed {

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
				// for (int i = 0; i < scp.length; i++)
				// for (int a = doms[i].first(); a != -1; a = doms[i].next(a))
				// if (!seekFirstSupportWith(i, a)) {
				// Kit.log.warning(" " + scp[i] + "=" + a + " not supported by " + this);
				// display(true);
				// return false;
				// }
				return true;
			}
		}
	}

	// ************************************************************************
	// ***** Classes for x = (y <op> z) (CtrPrimitiveTernaryLog)
	// ************************************************************************

	public static abstract class CtrPrimitiveTernaryLog extends CtrPrimitiveTernary
			implements TagGACGuaranteed, TagFilteringCompleteAtEachCall, TagUnsymmetric {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			assert op != null;
			if (op == LT)
				return pb.addCtr(new LogLT3(pb, x, y, z));
			if (op == LE)
				return pb.addCtr(new LogLE3(pb, x, y, z));
			if (op == GE)
				return pb.addCtr(new LogGE3(pb, x, y, z));
			if (op == GT)
				return pb.addCtr(new LogGT3(pb, x, y, z));
			if (op == EQ)
				pb.addCtr(new LogEQ3(pb, x, y, z));
			return pb.addCtr(new LogNE3(pb, x, y, z));
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
				if (dx.first() == 1) { // only 1 remaining => y < z
					if (dy.removeValuesGreaterThanOrEqual(dz.lastValue()) == false && dz.removeValuesLessThanOrEqual(dy.firstValue()) == false)
						return false;
				}
				if (dx.last() == 0) { // only 0 remaining => y >= z
					if (dy.removeValuesLessThan(dz.firstValue()) == false && dz.removeValuesGreaterThan(dy.lastValue()) == false)
						return false;
				}
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
				if (dx.first() == 1) { // only 1 remaining => y <= z
					if (dy.removeValuesGreaterThan(dz.lastValue()) == false && dz.removeValuesLessThan(dy.firstValue()) == false)
						return false;
				}
				if (dx.last() == 0) { // only 0 remaining => y > z
					if (dy.removeValuesLessThanOrEqual(dz.firstValue()) == false && dz.removeValuesGreaterThanOrEqual(dy.lastValue()) == false)
						return false;
				}
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
				if (dx.first() == 1) { // only 1 remaining => y >= z
					if (dy.removeValuesLessThan(dz.firstValue()) == false && dz.removeValuesGreaterThan(dy.lastValue()) == false)
						return false;
				}
				if (dx.last() == 0) { // only 0 remaining => y < z
					if (dy.removeValuesGreaterThanOrEqual(dz.lastValue()) == false && dz.removeValuesLessThanOrEqual(dy.firstValue()) == false)
						return false;
				}
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
				if (dx.first() == 1) { // only 1 remaining => y > z
					if (dy.removeValuesLessThanOrEqual(dz.firstValue()) == false && dz.removeValuesGreaterThanOrEqual(dy.lastValue()) == false)
						return false;
				}
				if (dx.last() == 0) { // only 0 remaining => y <= z
					if (dy.removeValuesGreaterThan(dz.lastValue()) == false && dz.removeValuesLessThan(dy.firstValue()) == false)
						return false;
				}
				return true;
			}
		}

		public static final class LogEQ3 extends CtrPrimitiveTernaryLog {

			int residue; // for a common value in the domains of y and z, supporting (x,0)

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] == t[2]);
			}

			public LogEQ3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.remove(dy.firstValue() == dz.firstValue() ? 0 : 1, false); // remember that indexes and values match for x
				if (dx.first() == 1) { // only 1 remaining => y = z
					if (dy.removeValuesNotIn(dz) == false)
						return false;
					assert dy.size() <= dz.size();
					if (dy.size() == dz.size())
						return true;
					boolean consistent = dz.removeValuesNotIn(dy);
					assert consistent;
					return true;
				}
				if (dx.last() == 0) { // only 0 remaining => y != z
					if (dy.size() == 1 && dz.removeValue(dy.uniqueValue(), false) == false)
						return false;
					if (dz.size() == 1 && dy.removeValue(dz.uniqueValue(), false) == false)
						return false;
					return true;
				}
				assert dx.size() == 2;
				// we know that 0 for x is supported because the domain of y or z is not singleton
				if (dy.isPresentValue(residue) && dz.isPresentValue(residue))
					return true;
				// we look for a support for (x,1), and record it as a residue
				for (int a = dy.first(); a != -1; a = dy.next(a)) {
					int va = dy.toVal(a);
					if (dy.isPresentValue(va)) {
						residue = va;
						return true;
					}
				}
				dx.removeSafely(1);
				return true;
			}
		}

		public static final class LogNE3 extends CtrPrimitiveTernaryLog {

			int residue; // for a common value in the domains of y and z, supporting (x,0)

			@Override
			public final boolean checkValues(int[] t) {
				return (t[0] == 1) == (t[1] != t[2]);
			}

			public LogNE3(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				if (dy.size() == 1 && dz.size() == 1)
					return dx.remove(dy.firstValue() != dz.firstValue() ? 0 : 1, false); // remember that indexes and values match for x
				if (dx.first() == 1) { // only 1 remaining => y != z
					if (dy.size() == 1 && dz.removeValue(dy.uniqueValue(), false) == false)
						return false;
					if (dz.size() == 1 && dy.removeValue(dz.uniqueValue(), false) == false)
						return false;
					return true;
				}
				if (dx.last() == 0) { // only 0 remaining => y = z
					if (dy.removeValuesNotIn(dz) == false)
						return false;
					assert dy.size() <= dz.size();
					if (dy.size() == dz.size())
						return true;
					boolean consistent = dz.removeValuesNotIn(dy);
					assert consistent;
					return true;
				}
				assert dx.size() == 2;
				// we know that 1 for x is supported because the domain of y or z is not singleton
				if (dy.isPresentValue(residue) && dz.isPresentValue(residue))
					return true;
				// we look for a support for (x,0), and record it as a residue
				for (int a = dy.first(); a != -1; a = dy.next(a)) {
					int va = dy.toVal(a);
					if (dy.isPresentValue(va)) {
						residue = va;
						return true;
					}
				}
				dx.removeSafely(0);
				return true;
			}
		}

	}

}
