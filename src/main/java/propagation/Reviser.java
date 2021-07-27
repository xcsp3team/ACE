/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import dashboard.Control.SettingPropagation;
import interfaces.FilteringSpecific;
import problem.Problem;
import sets.LinkedSet;
import sets.LinkedSetOrdered.LinkedSetOrderedWithBits2;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * A reviser is attached to a propagation technique and allows us to manage revisions (within a generic filtering scheme).
 */
public class Reviser { // Basic object to perform revisions, as in AC3

	/**
	 * The propagation technique to which the reviser is attached.
	 */
	protected Forward propagation;

	/**
	 * The number of revisions, i.e., the number of calls to <code> revise(c,x) </code>
	 */
	public long nRevisions, nUselessRevisions;

	public Reviser(Forward propagation) {
		this.propagation = propagation;
	}

	public boolean mustBeAppliedTo(Constraint c, Variable x) {
		return true;
	}

	public void applyTo(Constraint c, Variable x) {
		int px = c.positionOf(x);
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (!c.findArcSupportFor(px, a))
				x.dom.removeElementary(a);
		}
	}

	public final boolean revise(Constraint c, Variable x) {
		assert !x.assigned() && c.involves(x);
		if (mustBeAppliedTo(c, x)) {
			nRevisions++;
			int sizeBefore = x.dom.size();
			applyTo(c, x);
			int sizeAfter = x.dom.size();
			if (sizeBefore != sizeAfter)
				return propagation.handleReduction(x, sizeAfter);
			nUselessRevisions++;
		}
		return true;
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * Object used to perform revisions, exploiting pre-computed number of conflicts.
	 */
	public static class Reviser2 extends Reviser {

		public Reviser2(Forward propagation) {
			super(propagation);
		}

		@Override
		public boolean mustBeAppliedTo(Constraint c, Variable x) {
			if (c.conflictsStructure == null)
				return true;
			int px = c.positionOf(x);
			return c.conflictsStructure.nMaxConflicts[px] >= Domain.nValidTuplesBounded(c.doms, px);
		}

		@Override
		public void applyTo(Constraint c, Variable x) {
			if (c.conflictsStructure == null)
				super.applyTo(c, x);
			else {
				int px = c.positionOf(x);
				long nb = Domain.nValidTuplesBounded(c.doms, px);
				int[] nc = c.conflictsStructure.nConflicts[px];
				Domain dom = x.dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (nc[a] >= nb && !c.findArcSupportFor(px, a))
						x.dom.removeElementary(a);
			}
		}
	}

	/**
	 * Performing revisions using bitwise operations (when possible), as in AC3^bit+rm
	 */
	public static final class Reviser3 extends Reviser2 {
		final int residueLimitForBitRm = 499; // hard coding
		final int memoryLimitForBitRm = 550000000; // hard coding

		private final short[][][] bitRmResidues; // bitRmResidues[c][x][a]

		private boolean variant = false; // hard coding

		public Reviser3(Forward propagation) {
			super(propagation);
			Problem pb = propagation.solver.problem;
			SettingPropagation settings = pb.head.control.propagation;
			if (settings.bitResidues) {
				long nResidues = 0;
				this.bitRmResidues = new short[pb.constraints.length][][];
				int limit = residueLimitForBitRm;
				boolean stopped = false;
				for (Constraint c : pb.constraints) {
					if (c instanceof FilteringSpecific || !(c.extStructure() instanceof Bits))
						continue;
					int size0 = c.scp[0].dom.initSize(), size1 = c.scp[1].dom.initSize();
					bitRmResidues[c.num] = new short[2][];
					if (stopped)
						continue;
					if (size0 > limit)
						bitRmResidues[c.num][1] = new short[size1];
					if (size1 > limit)
						bitRmResidues[c.num][0] = new short[size0];
					nResidues += (size0 > limit ? size1 : 0) + (size1 > limit ? size0 : 0);
					if (nResidues * 2 + Kit.memory() > memoryLimitForBitRm) {
						Kit.log.info("Stop creating residues for RevisionManagerBitRm");
						stopped = true;
					}
				}
			} else
				this.bitRmResidues = null;
		}

		private short seekSupportPosition(long[] bitSup, long[] bitDom) {
			for (short i = 0; i < bitSup.length; i++)
				if ((bitSup[i] & bitDom[i]) != 0)
					return i;
			return -1;
		}

		private short seekSupportPosition(long[] bitSup, long[] bitDom, int[] bitSupDense, SetSparse set) { // for the variant
			if (set.size() <= bitSupDense.length) {
				int[] dense = set.dense;
				for (int i = set.limit; i >= 0; i--) {
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
			if (!(c.extStructure() instanceof Bits)) {
				super.applyTo(c, x);
				return;
			}
			// Bits implies that c is a binary constraint involving x and another variable y
			int px = c.positionOf(x);
			Domain dom = x.dom;
			Variable y = c.scp[px == 0 ? 1 : 0];
			long[] bitDom = y.dom.binary();
			long[][] bitSups = ((Bits) c.extStructure()).bitSupsFor(px);
			short[] residues = bitRmResidues != null ? bitRmResidues[c.num][px] : null;
			if (!variant) {
				if (residues != null) {
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						short i = residues[a];
						if ((bitSups[a][i] & bitDom[i]) != 0)
							continue;
						i = seekSupportPosition(bitSups[a], bitDom);
						if (i == -1)
							dom.removeElementary(a);
						else
							residues[a] = i;
					}
				} else
					for (int a = dom.first(); a != -1; a = dom.next(a))
						if (seekSupportPosition(bitSups[a], bitDom) == -1)
							dom.removeElementary(a);
			} else {
				LinkedSetOrderedWithBits2 sety = (LinkedSetOrderedWithBits2) ((LinkedSet) y.dom);
				int[][] bitSupsDense = ((Bits) c.extStructure()).bitSupsDenseFor(px);
				if (residues != null) {
					for (int a = dom.first(); a != -1; a = dom.next(a)) {
						short i = residues[a];
						if ((bitSups[a][i] & bitDom[i]) != 0)
							continue;
						i = seekSupportPosition(bitSups[a], bitDom, bitSupsDense[a], sety.set);
						if (i == -1)
							dom.removeElementary(a);
						else
							residues[a] = i;
					}
				} else
					for (int a = dom.first(); a != -1; a = dom.next(a))
						if (seekSupportPosition(bitSups[a], bitDom, bitSupsDense[a], sety.set) == -1)
							dom.removeElementary(a);
			}
		}
	}

}
