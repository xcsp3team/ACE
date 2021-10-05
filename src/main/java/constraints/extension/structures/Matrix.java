/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import java.util.stream.Stream;

import constraints.Constraint;
import constraints.ConstraintExtension;
import utility.Kit;

/**
 * This is the root class for extension structures represented by matrix forms. Currently, 2-dimensional and
 * 3-dimensional matrices are implemented.
 * 
 * @author Christophe Lecoutre
 */
public abstract class Matrix extends ExtensionStructure {

	public Matrix(ConstraintExtension c) {
		super(c);
	}

	/**
	 * A two-dimensional array for representing the semantics of a binary constraint
	 */
	public static final class Matrix2D extends Matrix {

		@Override
		public final boolean checkIndexes(int[] t) {
			return supports[t[0]][t[1]];
		}

		/**
		 * Supports[a][b] is 1 if the pair of value indexes (a,b) is a support of the binary constraint(s) registered
		 * with the structure
		 */
		protected boolean[][] supports;

		public Matrix2D(ConstraintExtension c) {
			super(c);
			Kit.control(c.scp.length == 2);
		}

		public Matrix2D(ConstraintExtension c, Matrix2D matrix2D) { // called by reflection when cloning structures
			this(c);
			this.supports = Stream.of(matrix2D.supports).map(t -> t.clone()).toArray(boolean[][]::new);
		}

		@Override
		public void storeTuples(int[][] tuples, boolean positive) {
			Constraint c = firstRegisteredCtr();
			this.supports = new boolean[c.doms[0].initSize()][c.doms[1].initSize()];
			if (!positive)
				Kit.fill(supports, true);
			for (int[] tuple : tuples)
				if (c.indexesMatchValues)
					supports[tuple[0]][tuple[1]] = positive;
				else
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])] = positive;
		}

		@Override
		public boolean removeTuple(int[] tuple) {
			assert registeredCtrs().size() == 1;
			int a = tuple[0], b = tuple[1];
			if (!supports[a][b])
				return false;
			supports[a][b] = false;
			incrementNbTuplesRemoved();
			return true;
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder("Matrix2D of " + firstRegisteredCtr() + "\n");
			for (boolean[] t : supports) {
				for (boolean b : t)
					sb.append(b ? "1" : "0");
				sb.append("\n");
			}
			return sb.toString();
		}
	}

	/**
	 * A three-dimensional array for representing the semantics of a ternary constraint
	 */
	public static final class Matrix3D extends Matrix {

		@Override
		public final boolean checkIndexes(int[] t) {
			return supports[t[0]][t[1]][t[2]];
		}

		/**
		 * Supports[a][b][c] is 1 if the triplet of value indexes (a,b,c) is a support of the ternary constraint(s)
		 * registered with the structure
		 */
		protected boolean[][][] supports;

		public Matrix3D(ConstraintExtension c) {
			super(c);
			Kit.control(c.scp.length == 3);
		}

		public Matrix3D(ConstraintExtension c, Matrix3D matrix3D) { // called by reflection when cloning structures
			this(c);
			this.supports = Stream.of(matrix3D.supports).map(m -> Stream.of(m).map(t -> t.clone()).toArray(boolean[][]::new)).toArray(boolean[][][]::new);
		}

		@Override
		public void storeTuples(int[][] tuples, boolean positive) {
			Constraint c = firstRegisteredCtr();
			this.supports = new boolean[c.doms[0].initSize()][c.doms[1].initSize()][c.doms[2].initSize()];
			if (!positive)
				for (boolean[][] m : supports)
					Kit.fill(m, true);
			for (int[] tuple : tuples)
				if (c.indexesMatchValues)
					supports[tuple[0]][tuple[1]][tuple[2]] = positive;
				else
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])][c.doms[2].toIdx(tuple[2])] = positive;
		}

		@Override
		public boolean removeTuple(int[] tuple) {
			assert registeredCtrs().size() == 1;
			int a = tuple[0], b = tuple[1], c = tuple[2];
			if (!supports[a][b][c])
				return false;
			supports[a][b][c] = false;
			incrementNbTuplesRemoved();
			return true;
		}
	}
}
