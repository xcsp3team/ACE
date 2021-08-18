package constraints.extension.structures;

import constraints.Constraint;
import constraints.ConstraintExtension;
import utility.Kit;

/**
 * This is the root class for the matrix forms of extension structures. Currently, 2-dimensional and 3-dimensional matrices are implemented.
 * 
 * @author Christophe Lecoutre
 *
 */
public abstract class Matrix extends ExtensionStructure {

	public Matrix(ConstraintExtension c) {
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
			for (int[] tuple : tuples)
				if (c.indexesMatchValues)
					supports[tuple[0]][tuple[1]] = positive;
				else
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])] = positive;
		}

		public Matrix2D(ConstraintExtension c) {
			super(c);
			Kit.control(c.scp.length == 2);
		}

		public Matrix2D(ConstraintExtension c, Matrix2D matrix2D) {
			this(c);
			this.supports = Kit.cloneDeeply(matrix2D.supports);
		}

		@Override
		public final boolean checkIndexes(int[] t) {
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
				Kit.fill(supports, true);
			for (int[] tuple : tuples)
				if (c.indexesMatchValues)
					supports[tuple[0]][tuple[1]][tuple[2]] = positive;
				else
					supports[c.doms[0].toIdx(tuple[0])][c.doms[1].toIdx(tuple[1])][c.doms[2].toIdx(tuple[2])] = positive;
		}

		public Matrix3D(ConstraintExtension c) {
			super(c);
			Kit.control(c.scp.length == 3);
		}

		public Matrix3D(ConstraintExtension c, Matrix3D matrix3D) {
			this(c);
			this.supports = Kit.cloneDeeply(matrix3D.supports);
		}

		@Override
		public final boolean checkIndexes(int[] t) {
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
