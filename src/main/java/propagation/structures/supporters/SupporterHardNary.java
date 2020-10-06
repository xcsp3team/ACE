/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.structures.supporters;

import java.util.stream.Stream;

import constraints.CtrHard;
import utility.Kit;

public final class SupporterHardNary extends SupporterHard {

	private final int[][][] residues;

	@Override
	public void reset() {
		Stream.of(residues).forEach(m -> Kit.fill(m, -1));
	}

	public SupporterHardNary(CtrHard c) {
		super(c);
		Kit.control(c.scp.length > 2);
		this.residues = Stream.of(c.scp).map(x -> Kit.repeat(-1, x.dom.initSize(), c.scp.length)).toArray(int[][][]::new);
	}

	@Override
	public boolean findArcSupportFor(int x, int a) {
		int q = x == 0 ? 1 : 0;
		int[] residue = residues[x][a];
		if (residue[q] != -1 && c.isValid(residue))
			return true;
		if (c.seekFirstSupportWith(x, a, buffer)) {
			if (multidirectionality)
				for (int i = 0; i < residues.length; i++)
					Kit.copy(buffer, residues[i][buffer[i]]);
			else
				Kit.copy(buffer, residues[x][a]);
			return true;
		}
		return false;
	}

}