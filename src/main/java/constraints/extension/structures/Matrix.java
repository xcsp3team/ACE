/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension.structures;

import constraints.Constraint;
import utility.Kit;

public abstract class Matrix extends ExtensionStructure {
	public Matrix(Constraint c) {
		super(c);
	}

	public static class Matrix2D extends Matrix {
		protected boolean[][] supports;

		@Override
		public void storeTuples(int[][] tuples, boolean positive) {
			Constraint c = firstRegisteredCtr();
			this.supports = new boolean[c.doms[0].initSize()][c.doms[1].initSize()];
			if (!positive)
				Kit.fill(supports, true);
			if (c.indexesMatchValues) {
				for (int[] tuple : tuples)
					supports[tuple[0]][tuple[1]] = positive;
			} else
				for (int[] tuple : tuples)
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])] = positive;
		}

		public Matrix2D(Constraint c) {
			super(c);
			Kit.control(c.scp.length == 2);
		}

		public Matrix2D(Constraint c, Matrix2D matrix2D) {
			this(c);
			this.supports = Kit.cloneDeeply(matrix2D.supports);
		}

		/**
		 * This method returns true iff all pairs of variable assignments corresponding to the tuple are compatible.
		 */
		@Override
		public final boolean checkIdxs(int[] t) {
			return supports[t[0]][t[1]];
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

	public static class Matrix3D extends Matrix {
		protected boolean[][][] supports;

		@Override
		public void storeTuples(int[][] tuples, boolean positive) {
			Constraint c = firstRegisteredCtr();
			this.supports = new boolean[c.doms[0].initSize()][c.doms[1].initSize()][c.doms[2].initSize()];
			if (!positive)
				for (int i = 0; i < supports.length; i++)
					for (int j = 0; j < supports[i].length; j++)
						for (int k = 0; k < supports[i][j].length; k++)
							supports[i][j][k] = true;

			if (c.indexesMatchValues) {
				for (int[] tuple : tuples)
					supports[tuple[0]][tuple[1]][tuple[2]] = positive;
			} else
				for (int[] tuple : tuples)
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])][c.doms[2].toIdx(tuple[2])] = positive;
		}

		public Matrix3D(Constraint c) {
			super(c);
			assert c.scp.length == 3;
		}

		public Matrix3D(Constraint c, Matrix3D matrix3D) {
			this(c);
			supports = Kit.cloneDeeply(matrix3D.supports);
		}

		@Override
		public final boolean checkIdxs(int[] t) {
			return supports[t[0]][t[1]][t[2]];
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
