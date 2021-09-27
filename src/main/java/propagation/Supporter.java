/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package propagation;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import interfaces.SpecificPropagator;
import propagation.Reviser.Reviser3;
import utility.Kit;
import variables.Variable;

public abstract class Supporter {

	public static Supporter buildFor(Constraint c) {
		if (c.problem.head.control.propagation.residues && c.scp.length > 1 && !(c instanceof SpecificPropagator)
				&& !(c.problem.head.control.propagation.reviser.equals(Reviser3.class.getSimpleName()) && c.extStructure() instanceof Bits)) {
			return c.scp.length == 2 ? new SupporterHardBary(c) : new SupporterHardNary(c);
		}
		return null;
	}

	/**
	 * The constraint to which this object is attached
	 */
	protected Constraint c;

	/**
	 * Indicates if multidirectionality of supports must be used
	 */
	protected boolean multidirectionality;

	/**
	 * A temporary array
	 */
	protected int[] buffer;

	public Supporter(Constraint c) {
		this.c = c;
		this.multidirectionality = c.problem.head.control.propagation.multidirectionality;
		this.buffer = c.tupleIterator.buffer;
	}

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	public static abstract class SupporterHard extends Supporter {

		/**
		 * MUST be called when the constraint relation is modified
		 */
		public abstract void reset();

		public SupporterHard(Constraint c) {
			super(c);
		}

		public abstract boolean findArcSupportFor(int x, int a);

	}

	public static final class SupporterHardBary extends SupporterHard {

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
			if (b != -1 && c.doms[q].contains(b)) {
				// if (c.problem.solver.propagation instanceof TagBinaryRelationFiltering) {
				// buffer[x] = a;
				// buffer[q] = b;
				// if (c.checkIndexes(buffer))
				// return true;
				// } else
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

	public static final class SupporterHardNary extends SupporterHard {

		private final int[][][] residues;

		@Override
		public void reset() {
			Stream.of(residues).forEach(m -> Kit.fill(m, -1));
		}

		public SupporterHardNary(Constraint c) {
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
}