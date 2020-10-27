/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import interfaces.TagGACUnguaranteed;
import interfaces.TagUnsymmetric;
import problem.Problem;
import variables.Variable;
import variables.domains.Domain;

public class EQADD extends CtrPrimitiveTernary implements TagUnsymmetric, TagGACUnguaranteed {

	@Override
	public final boolean checkValues(int[] vals) {
		return vals[0] == vals[1] + vals[2];
	}

	private final static int INF = 0, SUP = 1, NONE = Integer.MAX_VALUE;

	private int[][] residues = new int[3][2]; // residues[i] are for scp[i]

	public EQADD(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, x, y, z);
	}

	private boolean boundZ() {
		while (true) {
			int nb = pb.nValuesRemoved;
			// boundZ on sup values
			if (dx.removeValuesGT(dy.lastValue() + dz.lastValue()) == false)
				return false;
			if (dy.removeValuesGT(dx.lastValue() - dz.firstValue()) == false)
				return false;
			if (dz.removeValuesGT(dx.lastValue() - dy.firstValue()) == false)
				return false;
			// boundZ on inf values
			if (dx.removeValuesLT(dy.firstValue() + dz.firstValue()) == false)
				return false;
			if (dy.removeValuesLT(dx.firstValue() - dz.lastValue()) == false)
				return false;
			if (dz.removeValuesLT(dx.firstValue() - dy.lastValue()) == false)
				return false;
			if (nb == pb.nValuesRemoved)
				break;
		}
		return true;
	}

	private int seekBoundX(int bnd, Domain dom1, Domain dom2) {
		for (int idx = dom1.last(); idx != -1; idx = dom1.prev(idx)) {
			int val = dom1.toVal(idx);
			if (dom2.isPresentValue(bnd - val))
				return val;
			// else if (bnd-b > dom2.getLastVal()) return NONE; ATTENTION ordre du for et condition d'arret
		}
		return NONE;
	}

	private int seekBoundDSupportX(int bnd, int residue) {
		if (dy.isPresentValue(residue) && dz.isPresentValue(bnd - residue) || dz.isPresentValue(residue) && dy.isPresentValue(bnd - residue))
			return residue;
		return dy.size() < dz.size() ? seekBoundX(bnd, dy, dz) : seekBoundX(bnd, dz, dy);
	}

	private int seekBoundDSupportYZ(int bnd, int residue, Domain dom) {
		if (dx.isPresentValue(residue) && dom.isPresentValue(residue - bnd) || dom.isPresentValue(residue) && dx.isPresentValue(residue + bnd))
			return residue;
		if (dx.size() < dom.size()) {
			for (int idx = dx.last(); idx != -1; idx = dx.prev(idx)) {
				int val = dx.toVal(idx);
				if (dom.isPresentValue(val - bnd))
					return val;
				// else
			}
		} else {
			for (int idx = dom.last(); idx != -1; idx = dom.prev(idx)) {
				int val = dom.toVal(idx);
				if (dx.isPresentValue(val + bnd))
					return val;
				// else
			}
		}
		return NONE;
	}

	private Boolean manageBoundFor(int vap, int BND) {
		Domain dom = scp[vap].dom;
		int bnd = BND == INF ? dom.firstValue() : dom.lastValue();
		int support = dom == dx ? seekBoundDSupportX(bnd, residues[vap][BND]) : seekBoundDSupportYZ(bnd, residues[vap][BND], dom == dy ? dz : dy);
		if (support == NONE) {
			if (dom.removeValue(bnd) == false)
				return Boolean.FALSE;
			return null;
		} else
			residues[vap][BND] = support;
		return Boolean.TRUE;
	}

	private Boolean boundD() {
		Boolean b = manageBoundFor(0, INF);
		if (b != Boolean.TRUE)
			return b;
		b = manageBoundFor(0, SUP);
		if (b != Boolean.TRUE)
			return b;
		b = manageBoundFor(1, INF);
		if (b != Boolean.TRUE)
			return b;
		b = manageBoundFor(1, SUP);
		if (b != Boolean.TRUE)
			return b;
		b = manageBoundFor(2, INF);
		if (b != Boolean.TRUE)
			return b;
		b = manageBoundFor(2, SUP);
		if (b != Boolean.TRUE)
			return b;
		return Boolean.TRUE;
	}

	@Override
	public boolean runPropagator(Variable evt) {
		while (true) {
			if (boundZ() == false)
				return false;
			Boolean b = boundD();
			if (b == Boolean.FALSE)
				return false;
			if (b == Boolean.TRUE)
				break;
		}
		return true;
	}

	// public DefXCSP defXCSP() {
	// return new DefXCSP(INTENSION).addChild(FUNCTION, pb.ui.eq(x, pb.ui.add(y, z)));
	// }
}
