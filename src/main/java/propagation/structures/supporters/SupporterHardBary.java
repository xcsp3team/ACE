/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.supporters;

import constraints.Constraint;
import interfaces.TagBinaryRelationFiltering;
import utility.Kit;
import variables.Variable;

public final class SupporterHardBary extends SupporterHard {

	public final int[][] residues;

	@Override
	public void reset() {
		Kit.fill(residues, -1);
	}

	public SupporterHardBary(Constraint c) {
		super(c);
		Kit.control(c.scp.length == 2);
		this.residues = Variable.litterals(c.scp).intArray(-1);
	}

	@Override
	public boolean findArcSupportFor(int x, int a) {
		int q = x == 0 ? 1 : 0;
		int b = residues[x][a];
		if (b != -1 && c.doms[q].isPresent(b)) {
			if (c.pb.solver.propagation instanceof TagBinaryRelationFiltering) {
				buffer[x] = a;
				buffer[q] = b;
				if (c.checkIndexes(buffer))
					return true;
			} else
				return true;
		}
		if (c.seekFirstSupportWith(x, a, buffer)) {
			b = buffer[q];
			residues[x][a] = b;
			if (multidirectionality)
				residues[q][b] = a;
			return true;
		}
		return false;
	}

}