/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import interfaces.SpecificPropagator;
import problem.Problem;
import sets.SetLinked;
import sets.SetLinkedFinite.SetLinkedFiniteWithBits2;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * A reviser is attached to a propagation technique and allows us to manage revisions (within a generic filtering scheme). If all constraints have specific
 * propagators, this kind of object is not used.
 * 
 * @author Christophe Lecoutre
 */
public class Reviser { // Basic object to perform revisions, as in AC3

	/**
	 * The propagation technique to which the reviser is attached.
	 */
	protected Forward propagation;

	/**
	 * The number of revisions, i.e., the number of calls to <code> revise(c,x) </code>
	 */
	public long nRevisions;

	/**
	 * The number of useless revisions, i.e., the number of calls to <code> revise(c,x) </code> that leads to no inference (value removal)
	 */
	public long nUselessRevisions;

	/**
	 * Builds a reviser for the specified propagation object
	 * 
	 * @param propagation
	 *            an object managing constraint propagation
	 */
	public Reviser(Forward propagation) {
		this.propagation = propagation;
	}

	/**
	 * Returns true if the revision of the domain of the specified variable should be executed for the specified constraint
	 * 
	 * @param c
	 *            a constraint
	 * @param x
	 *            a variable involved in the constraint
	 * @return true if the revision should be executed
	 */
	public boolean mustBeAppliedTo(Constraint c, Variable x) {
		return true;
	}

	/**
	 * Applies the revision of the domain of the specified variable in the specified constraint
	 * 
	 * @param c
	 *            a constraint
	 * @param x
	 *            a variable involved in the constraint
	 */
	public void applyTo(Constraint c, Variable x) {
		int i = c.positionOf(x);
		Domain dom = x.dom;
		for (int a = dom.first(); a != -1; a = dom.next(a)) {
			if (!c.findArcSupportFor(i, a))
				dom.removeElementary(a);
		}
	}

	/**
	 * Revises the domain of the specified variable for the specified constraint, and returns false if an inconsistency is detected. In some cases, the revision
	 * can be avoided (because proved as useless).
	 * 
	 * @param c
	 *            a constraint
	 * @param x
	 *            a variable involved in the constraint
	 * @return false iff an inconsistency is detected
	 */
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
	 * A revision object that exploits pre-computed number of conflicts.
	 */
	public static class Reviser2 extends Reviser {

		public Reviser2(Forward propagation) {
			super(propagation);
		}

		@Override
		public boolean mustBeAppliedTo(Constraint c, Variable x) {
			if (c.conflictsStructure == null)
				return true;
			int i = c.positionOf(x);
			return c.conflictsStructure.nMaxConflicts[i] >= Domain.nValidTuplesBounded(c.doms, i);
		}

		@Override
		public void applyTo(Constraint c, Variable x) {
			if (c.conflictsStructure == null)
				super.applyTo(c, x);
			else {
				int i = c.positionOf(x);
				long nb = Domain.nValidTuplesBounded(c.doms, i);
				int[] nc = c.conflictsStructure.nConflicts[i];
				Domain dom = x.dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					if (nc[a] >= nb && !c.findArcSupportFor(i, a))
						dom.removeElementary(a);
			}
		}
	}

	/**
	 * A revision object that performs revisions using bitwise operations (when possible), as in AC3^bit+rm
	 */
	public static final class Reviser3 extends Reviser2 {

		/**
		 * bitRmResidues[c][x][a] is the residue for the (value) index a of variable x in constraint c
		 */
		private final short[][][] bitRmResidues;

		private final int residueLimit = 499; // hard coding

		private final int memoryLimit = 550000000; // hard coding

		private boolean variant = false; // hard coding

		public Reviser3(Forward propagation) {
			super(propagation);
			Problem pb = propagation.solver.problem;
			if (pb.head.control.propagation.bitResidues) {
				long nResidues = 0;
				this.bitRmResidues = new short[pb.constraints.length][][];
				int limit = residueLimit;
				boolean stopped = false;
				for (Constraint c : pb.constraints) {
					if (c instanceof SpecificPropagator || !(c.extStructure() instanceof Bits))
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
					if (nResidues * 2 + Kit.memory() > memoryLimit) {
						Kit.log.info("Stop creating residues for RevisionManagerBitRm");
						stopped = true;
					}
				}
			} else
				this.bitRmResidues = null;
		}

		private short seekSupportPosition(long[] bitSup, long[] bitDom) {
			for (short i = 0; i < bitSup.length; i++) {
				if ((bitSup[i] & bitDom[i]) != 0)
					return i;
			}
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
			long[][] bitSups = ((Bits) c.extStructure()).sups(px);
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
				SetLinkedFiniteWithBits2 sety = (SetLinkedFiniteWithBits2) ((SetLinked) y.dom);
				int[][] bitSupsDense = ((Bits) c.extStructure()).supsFiletered(px);
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
