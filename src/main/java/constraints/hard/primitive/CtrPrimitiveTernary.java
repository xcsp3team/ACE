/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import constraints.hard.global.SumWeighted;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.Kit;
import utility.exceptions.MissingImplementationException;
import variables.Variable;
import variables.domains.Domain;

public abstract class CtrPrimitiveTernary extends CtrPrimitive { // implements TagGuaranteedGAC

	protected final Variable x, y, z;

	protected Domain domx, domy, domz;

	public CtrPrimitiveTernary(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, pb.api.vars(x, y, z));
		this.x = x;
		this.y = y;
		this.z = z;
		this.domx = x.dom;
		this.domy = y.dom;
		this.domz = z.dom;
	}

	public static abstract class CtrPrimitiveTernaryAdd extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new TernaryEQ(pb, x, y, z));
			else
				return pb.addCtr(SumWeighted.buildFrom(pb, pb.api.vars(x, y, z), pb.api.vals(1, 1, -1), op, 0));
		}

		public CtrPrimitiveTernaryAdd(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class TernaryEQ extends CtrPrimitiveTernary implements TagGACGuaranteed {

			int[] resx, resy, resz; // residues for values in the domains of x, y and z

			boolean multidirectional = false; // hard coding

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] + t[1] == t[2];
			}

			public TernaryEQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				this.resx = Kit.repeat(-1, domx.initSize());
				this.resy = Kit.repeat(-1, domy.initSize());
				this.resz = Kit.repeat(-1, domz.initSize());
			}

			@Override
			public Boolean isSymmetric() {
				return false;
			}

			// using labels and continue label is very inefficient. is that sure?

			@Override
			public boolean runPropagator(Variable dummy) {
				extern: for (int a = domx.first(); a != -1; a = domx.next(a)) {
					int va = domx.toVal(a);
					if (resx[a] != -1 && domy.isPresent(resx[a]) && domz.isPresentValue(va + domy.toVal(resx[a])))
						continue;
					// boolean found = false;
					for (int b = domy.first(); b != -1; b = domy.next(b)) {
						int vc = va + domy.toVal(b);
						if (vc > domz.lastValue())
							break;
						if (domz.isPresentValue(vc)) {
							resx[a] = b;
							if (multidirectional) {
								resy[b] = a;
								resz[domz.toIdx(vc)] = a;
							}
							continue extern;
							// found = true;
							// break;
						}
					}
					// if (!found && domx.remove(a) == false)
					if (domx.remove(a) == false)
						return false;
				}
				extern: for (int b = domy.first(); b != -1; b = domy.next(b)) {
					int vb = domy.toVal(b);
					if (resy[b] != -1 && domx.isPresent(resy[b]) && domz.isPresentValue(vb + domx.toVal(resy[b])))
						continue;
					// boolean found = false;
					for (int a = domx.first(); a != -1; a = domx.next(a)) {
						int vc = vb + domx.toVal(a);
						if (vc > domz.lastValue())
							break;
						if (domz.isPresentValue(vc)) {
							resy[b] = a;
							if (multidirectional)
								resz[domz.toIdx(vc)] = a;
							continue extern;
							// found = true;
							// break;
						}
					}
					// if (!found && domy.remove(b) == false)
					if (domy.remove(b) == false)
						return false;
				}
				extern: for (int c = domz.first(); c != -1; c = domz.next(c)) {
					int vc = domz.toVal(c);
					if (resz[c] != -1 && domx.isPresent(resz[c]) && domy.isPresentValue(vc - domx.toVal(resz[c])))
						continue;
					// boolean found = false;
					for (int a = domx.last(); a != -1; a = domx.prev(a)) {
						int vb = vc - domx.toVal(a);
						if (vb > domy.lastValue())
							break;
						if (domy.isPresentValue(vb)) {
							resz[c] = a;
							continue extern;
							// found = true;
							// break;
						}
					}
					// if (!found &&domz.remove(c) == false)
					if (domz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

	public static abstract class CtrPrimitiveTernaryMod extends CtrPrimitiveTernary {

		public static CtrAlone buildFrom(Problem pb, Variable x, Variable y, TypeConditionOperatorRel op, Variable z) {
			if (op == TypeConditionOperatorRel.EQ)
				return pb.addCtr(new TernaryModEQ(pb, x, y, z));
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryMod(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class TernaryModEQ extends CtrPrimitiveTernary implements TagGACGuaranteed {

			int[] resx, resy, resz1, resz2; // residues for values in the domains of x, y and z

			@Override
			public final boolean checkValues(int[] t) {
				return t[0] % t[1] == t[2];
			}

			public TernaryModEQ(Problem pb, Variable x, Variable y, Variable z) {
				super(pb, x, y, z);
				Kit.control(x.dom.firstValue() >= 0 && y.dom.firstValue() > 0 && z.dom.firstValue() >= 0);
				this.resx = Kit.repeat(-1, domx.initSize());
				this.resy = Kit.repeat(-1, domy.initSize());
				this.resz1 = Kit.repeat(-1, domz.initSize());
				this.resz2 = Kit.repeat(-1, domz.initSize());
			}

			@Override
			public Boolean isSymmetric() {
				return false;
			}

			@Override
			public boolean runPropagator(Variable dummy) {
				for (int a = domx.first(); a != -1; a = domx.next(a)) {
					int va = domx.toVal(a);
					if (va < domy.lastValue() && domz.isPresentValue(va)) // remainder in z is then necessarily va
						continue;
					if (resx[a] != -1 && domy.isPresent(resx[a]) && domz.isPresentValue(va % domy.toVal(resx[a])))
						continue;
					boolean found = false;
					for (int b = domy.first(); b != -1; b = domy.next(b)) {
						int vb = domy.toVal(b);
						if (va < vb) // means that the remainder with remaining values of y lead to va (and this has been considered earlier)
							break;
						if (domz.isPresentValue(va % vb)) {
							resx[a] = b;
							found = true;
							break;
						}
					}
					if (!found && domx.remove(a) == false)
						return false;
				}
				for (int b = domy.first(); b != -1; b = domy.next(b)) {
					int vb = domy.toVal(b);
					boolean found = false;
					if (vb <= domz.firstValue()) {
						if (domy.remove(b) == false)
							return false;
						continue;
					}
					if (resy[b] != -1 && domx.isPresent(resy[b]) && domz.isPresentValue(domx.toVal(resy[b]) % vb))
						continue;

					for (int a = domx.first(); a != -1; a = domx.next(a)) {
						int vc = domx.toVal(a) % vb;
						if (domz.isPresentValue(vc)) {
							resy[b] = a;
							found = true;
							break;
						}
					}
					if (!found && domy.remove(b) == false)
						return false;
				}
				if (domz.removeValues(TypeOperatorRel.GE, domy.lastValue()) == false) // because remainder is less than the denominator
					return false;
				for (int c = domz.first(); c != -1; c = domz.next(c)) {
					int vc = domz.toVal(c);
					if (resz1[c] != -1 && domx.isPresent(resz1[c]) && domy.isPresent(resz2[c]))
						continue;
					boolean found = false;
					for (int b = domy.last(); b != -1; b = domy.prev(b)) {
						int vb = domy.toVal(b);
						if (vb < vc)
							break;
						int nMultiples = domx.lastValue() / vb;
						if (domx.size() <= nMultiples) {
							for (int a = domx.first(); a != -1; a = domx.next(a)) {
								if (domx.toVal(a) % vb == vc) {
									resz1[c] = a;
									resz2[c] = b;
									found = true;
									break;
								}
							}
						} else {
							int multiple = vc;
							while (true) {
								if (multiple > domx.lastValue())
									break;
								if (domx.isPresentValue(multiple)) {
									resz1[c] = domx.toIdx(multiple);
									resz2[c] = b;
									found = true;
									break;
								}
								multiple += vb;
							}
						}
						if (found)
							break;

					}
					if (!found && domz.remove(c) == false)
						return false;
				}
				return true;
			}
		}
	}

}
