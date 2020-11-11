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
import constraints.extension.structures.Bits;
import interfaces.FilteringSpecific;
import propagation.order1.PropagationForward;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

/**
 * Performing revisions using bitwise operations (when possible), as in AC3^bit+rm
 */
public final class Reviser3 extends Reviser2 {

	private short[][][] bitRmResidues; // 1d = constraint num; 2D = variable position ; 3D = index

	public Reviser3(PropagationForward propagation) {
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

	private short seekSupportPosition(long[] bitSup, long[] bitDom) {
		// if ((cnt++) % 100000000 == 0)
		// System.out.println("cntSeek=" + cnt);
		for (short i = 0; i < bitSup.length; i++)
			if ((bitSup[i] & bitDom[i]) != 0)
				return i;
		return -1;
	}

	@Override
	public void applyTo(Constraint c, Variable x) {
		if (!(c.extStructure() instanceof Bits))
			super.applyTo(c, x);
		else {
			int px = c.positionOf(x);
			Domain dom = x.dom;
			long[] bitDom = c.scp[px == 0 ? 1 : 0].dom.binaryRepresentation();
			long[][] bitSups = ((Bits) c.extStructure()).bitSupsFor(px);
			short[][] residues = c.num < bitRmResidues.length ? bitRmResidues[c.num] : null; // TODO
			if (residues != null && residues[px] != null) {
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					short i = residues[px][a];
					if ((bitSups[a][i] & bitDom[i]) != 0)
						continue;
					i = seekSupportPosition(bitSups[a], bitDom);
					if (i == -1)
						dom.removeElementary(a);
					else
						residues[px][a] = i;
				}
			} else
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (seekSupportPosition(bitSups[a], bitDom) == -1)
						dom.removeElementary(a);
		}
	}
}
