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
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

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
			throw new MissingImplementationException();
		}

		public CtrPrimitiveTernaryAdd(Problem pb, Variable x, Variable y, Variable z) {
			super(pb, x, y, z);
		}

		public static final class TernaryEQ extends CtrPrimitiveTernary implements TagGACGuaranteed {

			int[] resx, resy, resz; // residues for values in the domains of x, y and z

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

			@Override
			public boolean runPropagator(Variable dummy) {
				for (int a = domx.first(); a != -1; a = domx.next(a)) {
					int v = domx.toVal(a);
					if (resx[a] != -1 && domy.isPresent(resx[a]))
						if (domz.isPresentValue(v + domy.toVal(resx[a])))
							continue;
					boolean found = false;
					for (int b = domy.first(); b != -1; b = domy.next(b)) {
						int w = v + domy.toVal(b);
						if (w > domz.lastValue()) {
							// if (domx.remove(a) == false)
							// return false;
							break;
						}
						if (domz.isPresentValue(w)) {
							resx[a] = b;
							found = true;
							break;
						}
					}
					if (!found && domx.remove(a) == false)
						return false;
				}
				for (int b = domy.first(); b != -1; b = domy.next(b)) {
					int v = domy.toVal(b);
					if (resy[b] != -1 && domx.isPresent(resy[b]))
						if (domz.isPresentValue(v + domx.toVal(resy[b])))
							continue;
					boolean found = false;
					for (int a = domx.first(); a != -1; a = domx.next(a)) {
						int w = v + domx.toVal(a);
						if (w > domz.lastValue()) {
							// if (domy.remove(b) == false)
							// return false;
							break;
						}
						if (domz.isPresentValue(w)) {
							resy[b] = a;
							found = true;
							break;
						}
					}
					if (!found && domy.remove(b) == false)
						return false;
				}
				for (int c = domz.first(); c != -1; c = domz.next(c)) {
					int v = domz.toVal(c);
					if (resz[c] != -1 && domx.isPresent(resz[c]))
						if (domy.isPresentValue(v - domx.toVal(resz[c])))
							continue;
					boolean found = false;
					for (int a = domx.last(); a != -1; a = domx.prev(a)) {
						int w = v - domx.toVal(a);
						if (w > domy.lastValue()) {
							// if (domz.remove(c) == false)
							// return false;
							break;
						}
						if (domy.isPresentValue(w)) {
							resz[c] = a;
							found = true;
							break;
						}
					}
					if (!found && domz.remove(c) == false)
						return false;
				}
				// System.out.println(this + " hereee");
				// for (int i = 0; i < scp.length; i++)
				// for (int a = doms[i].first(); a != -1; a = doms[i].next(a))
				// if (!seekFirstSupportWith(i, a)) {
				// Kit.log.warning(" " + scp[i] + "=" + a + " not supported by " + this);
				// display(true);
				// return false;
				// }
				// this.controlArcConsistency();
				return true;
			}
		}
	}

}
