/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.structures.revisers;

import constraints.Constraint;
import constraints.hard.extension.structures.Bits;
import interfaces.FilteringSpecific;
import propagation.order1.PropagationForward;
import utility.Kit;
import utility.sets.LinkedSet;
import utility.sets.LinkedSetOrdered.LinkedSetOrderedWithBits2;
import utility.sets.SetSparse;
import variables.Variable;
import variables.domains.Domain;

/**
 * Performing revisions using bitwise operations (when possible), as in AC3^bit+rm
 */
public final class Reviser4 extends Reviser2 {

	private short[][][] bitRmResidues; // 1d = constraint num; 2D = variable position ; 3D = index

	public Reviser4(PropagationForward propagation) {
		super(propagation);
		long nbResidues = 0;
		if (!propagation.solver.rs.cp.settingPropagation.bitResidues) {
			bitRmResidues = new short[0][][];
			return;
		}
		bitRmResidues = new short[propagation.pb().constraints.length][][];
		for (Constraint c : propagation.pb().constraints) {
			if (c instanceof FilteringSpecific)
				continue;
			if (c.extStructure() instanceof Bits) {
				int size0 = c.scp[0].dom.initSize(), size1 = c.scp[1].dom.initSize();
				bitRmResidues[c.num] = new short[2][];
				if (size0 > propagation.cp().settingPropagation.residueLimitForBitRm)
					bitRmResidues[c.num][1] = new short[size1];
				if (size1 > propagation.cp().settingPropagation.residueLimitForBitRm)
					bitRmResidues[c.num][0] = new short[size0];
				nbResidues += (size0 > propagation.cp().settingPropagation.residueLimitForBitRm ? size1 : 0)
						+ (size1 > propagation.cp().settingPropagation.residueLimitForBitRm ? size0 : 0);
			}
			if (nbResidues * 2 + Kit.getUsedMemory() > propagation.cp().settingPropagation.memoryLimitForBitRm) {
				Kit.log.info("Stop creating residues for RevisionManagerBitRm");
				break;
			}
		}
	}

	private short seekSupportPosition(long[] bitSup, int[] bitSupDense, long[] bitDom, SetSparse sset) {
		if (sset.size() <= bitSupDense.length) {
			int[] dense = sset.dense;
			for (int i = sset.limit; i >= 0; i--) {
				int j = dense[i];
				if ((bitSup[j] & bitDom[j]) != 0)
					return (short) j;
			}
		} else {
			for (int i = bitSupDense.length - 1; i >= 0; i--) {
				int j = bitSupDense[i];
				if ((bitSup[j] & bitDom[j]) != 0)
					return (short) j;
			}
		}
		return -1;
	}

	@Override
	public void applyTo(Constraint c, Variable x) {
		if (!(c.extStructure() instanceof Bits))
			super.applyTo(c, x);
		else {
			int px = c.positionOf(x);
			Domain dx = x.dom;
			Variable y = c.scp[px == 0 ? 1 : 0];
			LinkedSetOrderedWithBits2 sety = (LinkedSetOrderedWithBits2) ((LinkedSet) y.dom);
			long[] bitDom = y.dom.binaryRepresentation();
			long[][] bitSups = ((Bits) c.extStructure()).bitSupsFor(px);
			int[][] bitSupsDense = ((Bits) c.extStructure()).bitSupsDenseFor(px);
			short[][] residues = c.num < bitRmResidues.length ? bitRmResidues[c.num] : null; // TODO
			if (residues != null && residues[px] != null) {
				for (int a = dx.first(); a != -1; a = dx.next(a)) {
					short i = residues[px][a];
					if ((bitSups[a][i] & bitDom[i]) != 0)
						continue;
					i = seekSupportPosition(bitSups[a], bitSupsDense[a], bitDom, sety.sset);
					if (i == -1)
						x.dom.removeElementary(a);
					else
						residues[px][a] = i;
				}
			} else
				for (int a = dx.first(); a != -1; a = dx.next(a))
					if (seekSupportPosition(bitSups[a], bitSupsDense[a], bitDom, sety.sset) == -1)
						x.dom.removeElementary(a);
		}
	}
}
