/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import interfaces.FilteringSpecific;
import interfaces.TagBinaryRelationFiltering;
import propagation.Reviser.Reviser3;
import utility.Kit;
import variables.Variable;

public abstract class Supporter {

	public static Supporter buildFor(Constraint c) {
		if (c.pb.rs.cp.settingPropagation.residues && c.scp.length > 1 && !(c instanceof FilteringSpecific)
				&& !(c.pb.rs.cp.settingPropagation.classForRevisions.equals(Reviser3.class.getSimpleName()) && c.extStructure() instanceof Bits)) {
			return c.scp.length == 2 ? new SupporterHardBary(c) : new SupporterHardNary(c);
		} else
			return null;
	}

	protected Constraint c;

	protected boolean multidirectionality;

	protected int[] buffer;

	public Supporter(Constraint c) {
		this.c = c;
		this.multidirectionality = c.pb.rs.cp.settingPropagation.multidirectionality;
		this.buffer = c.tupleManager.localTuple;
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

		public boolean findArcSupportFor(Variable x, int a) {
			return findArcSupportFor(c.positionOf(x), a);
		}
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