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

import static utility.Kit.control;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.extension.structures.Bits;
import interfaces.SpecificPropagator;
import propagation.Reviser.Reviser3;
import utility.Kit;

/**
 * A "supporter" is attached to a constraint and allows us to benefit from residues (which are like cache) when looking
 * for supports of values (within a generic filtering scheme). If all constraints have specific propagators, this kind
 * of object is not used.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Supporter {

	/**
	 * Builds an object that is useful to look efficiently for supports, because benefiting from residues and
	 * multidirectionality
	 * 
	 * @param c
	 *            a constraint
	 * @return an object managing residues and multidirectionality
	 */
	public static Supporter buildFor(Constraint c) {
		if (c instanceof SpecificPropagator)
			return null;
		if (c.problem.head.control.propagation.residues == false || c.scp.length == 1)
			return null;
		if  (c.problem.head.control.propagation.reviser.equals(Reviser3.class.getSimpleName()) && c.extStructure() instanceof Bits) 
			return null;
		return c.scp.length == 2 ? new SupporterBary(c) : new SupporterNary(c);
		
//		if (c.problem.head.control.propagation.residues && c.scp.length > 1 && !(c instanceof SpecificPropagator)
//				&& !(c.problem.head.control.propagation.reviser.equals(Reviser3.class.getSimpleName()) && c.extStructure() instanceof Bits)) {
//			return c.scp.length == 2 ? new SupporterBary(c) : new SupporterNary(c);
//		}
//		return null;
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
	 * Builds an object that is useful for efficiently looking for supports of values
	 * 
	 * @param c
	 *            a constraint
	 */
	public Supporter(Constraint c) {
		this.c = c;
		this.multidirectionality = c.problem.head.control.propagation.multidirectionality;
	}

	/**
	 * Returns true if a support can be found for (x,a) on c
	 * 
	 * @param x
	 *            a variable involved in the constraint c
	 * @param a
	 *            a value index for x
	 * @return true if a support can be found for (x,a) on c
	 */
	public abstract boolean findArcSupportFor(int x, int a);

	/**********************************************************************************************
	 * Subclasses
	 *********************************************************************************************/

	/**
	 * Supporter for a binary constraint
	 */
	public static final class SupporterBary extends Supporter {

		/**
		 * residues[x][a] is the residue (last found support) for (x,a); this is a value index in the domain of the
		 * second variable y involved in the constraint c
		 */
		private final int[][] residues;

		public SupporterBary(Constraint c) {
			super(c);
			control(c.scp.length == 2);
			this.residues = Stream.of(c.scp).map(x -> Kit.repeat(-1, x.dom.initSize())).toArray(int[][]::new); // Variable.litterals(c.scp).intArray(-1);
		}

		@Override
		public boolean findArcSupportFor(int x, int a) {
			int y = x == 0 ? 1 : 0;
			int b = residues[x][a];
			if (b != -1 && c.doms[y].contains(b)) {
				// note that if we would dynamically modify the relation, we would need to check again validity
				return true;
			}
			if (c.seekFirstSupportWith(x, a)) {
				b = c.tupleIterator.buffer[y]; // the support is in the buffer of tupleIterator
				residues[x][a] = b;
				if (multidirectionality)
					residues[y][b] = a;
				return true;
			}
			return false;
		}
	}

	/**
	 * Supporter for a non binary constraint (i.e., a constraint wit an arity strictly greater than 2)
	 */
	public static final class SupporterNary extends Supporter {

		/**
		 * residues[x][a] is the residue (last found support) for (x,a); this is a tuple of value indexes, one for each
		 * variable involved in the constraint c
		 */
		private final int[][][] residues;

		public SupporterNary(Constraint c) {
			super(c);
			control(c.scp.length > 2);
			this.residues = Stream.of(c.scp).map(x -> IntStream.range(0, x.dom.initSize()).mapToObj(a -> Kit.repeat(-1, c.scp.length)).toArray(int[][]::new))
					.toArray(int[][][]::new);
		}

		@Override
		public boolean findArcSupportFor(int x, int a) {
			int[] residue = residues[x][a];
			if (residue[0] != -1 && c.isValid(residue))
				return true;
			if (c.seekFirstSupportWith(x, a)) {
				int[] buffer = c.tupleIterator.buffer; // the support is in the buffer of tupleIterator
				if (multidirectionality)
					for (int y = 0; y < residues.length; y++)
						Kit.copy(buffer, residues[y][buffer[y]]);
				else
					Kit.copy(buffer, residues[x][a]);
				return true;
			}
			return false;
		}

	}
}