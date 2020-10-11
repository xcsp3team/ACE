/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package search.backtrack.decomposers;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.CtrHard;
import heuristics.values.HeuristicValuesDynamic.Aic;
import problem.Problem;
import propagation.soft.pfc.RDAC;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class Decomposer {

	protected SolverBacktrackDecomposing solver;

	public Decomposer(SolverBacktrackDecomposing solver) {
		this.solver = solver;
	}

	protected BigInteger nMaxValidTuples() {
		return Stream.of(solver.pb.constraints).map(c -> Variable.nValidTuples(c.scp, false)).max(BigInteger::compareTo).get();
	}

	public abstract int getNbPieces();

	public abstract void initialize(Variable var);

	public abstract void split();

	public abstract int buildPiece(int num);

	public static class DecomposerVoid extends Decomposer {

		@Override
		public int getNbPieces() {
			return 1;
		}

		@Override
		public void initialize(Variable x) {}

		@Override
		public void split() {}

		@Override
		public int buildPiece(int num) {
			return 1;
		}

		public DecomposerVoid(SolverBacktrackDecomposing solver) {
			super(solver);
		}
	}

	public static class DecomposerSplitter extends Decomposer {
		private Variable var;

		private int nbPieces;

		private Variable varo;

		private int[] t;

		private int tlength;

		public DecomposerSplitter(SolverBacktrackDecomposing solver) {
			super(solver);
			t = new int[nMaxValidTuples().intValueExact()];
		}

		@Override
		public int getNbPieces() {
			return nbPieces;
		}

		@Override
		public void initialize(Variable var) {
			this.var = var;
		}

		@Override
		public void split() {
			varo = solver.heuristicVars.bestVar();
			Domain dom = varo.dom;
			int size = dom.size();
			if (varo == var || size == 1)
				nbPieces = 1;
			else {
				int i = 0;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					t[i++] = a;
				tlength = i;
				nbPieces = 2;
			}
		}

		@Override
		public int buildPiece(int num) {
			if (nbPieces == 1)
				return 1;
			if (num == 0) {
				for (int i = 0; i < tlength / 2; i++)
					varo.dom.removeElementary(t[i]);
			} else {
				for (int i = tlength / 2; i < tlength; i++)
					varo.dom.removeElementary(t[i]);
			}
			return solver.propagation.runAfterRefutation(varo) ? 1 : 0;
		}
	}

	public static class DecomposerRDAC1 extends Decomposer {

		private RDAC rdac;

		private int[] idOfACNeighbors; // 1D = order ; value = id of a neighbor AC

		private int[] nbConsistentValuesOfACNeighbors; // 1D = order ; value = nb values consistent of the ith neighbor AC

		private int[][] consistentValuesOfACNeighbors;

		private int nbPieces;

		public DecomposerRDAC1(SolverBacktrackDecomposing solver) {
			super(solver);
			Problem problem = solver.pb;
			idOfACNeighbors = new int[problem.stuff.maxVarDegree()];
			nbConsistentValuesOfACNeighbors = new int[problem.stuff.maxVarDegree()];
			consistentValuesOfACNeighbors = new int[problem.stuff.maxVarDegree()][nMaxValidTuples().intValueExact()];
			this.rdac = (RDAC) solver.propagation;
			Kit.control(problem.variables[0].heuristicVal instanceof Aic);
		}

		@Override
		public int getNbPieces() {
			return nbPieces;
		}

		@Override
		public void initialize(Variable x) {
			int a = x.heuristicVal.bestIndex();

			rdac.init(false);
			assert rdac.control();

			long[][][] minCosts = rdac.minCosts; // ((MaxCSP) getSearchPropagationTechnique()).getInconsistent();
			assert rdac.control();
			int nbACNeighbors = 0;
			for (Constraint c : x.ctrs) {
				int i = c.num;
				int j = c.positionOf(x);
				if (minCosts[i][j][a] > 0)
					continue;
				int neighborPosition = j == 0 ? 1 : 0;
				Variable neighbor = c.scp[neighborPosition];
				if (neighbor.isAssigned())
					continue;
				idOfACNeighbors[nbACNeighbors] = neighbor.num;
				int cnt = 0;
				int[] t = consistentValuesOfACNeighbors[nbACNeighbors];
				int[] tmp = c.tupleManager.localTuple;
				tmp[j] = a;
				Domain dom = neighbor.dom;
				for (int b = dom.first(); b != -1; b = dom.next(b)) {
					tmp[neighborPosition] = b;
					if (((CtrHard) c).checkIndexes(tmp))
						t[cnt++] = b;
				}
				nbConsistentValuesOfACNeighbors[nbACNeighbors] = cnt;
				nbACNeighbors++;
			}
			nbPieces = nbACNeighbors;
		}

		@Override
		public void split() {}

		@Override
		public int buildPiece(int num) {
			Variable[] variables = solver.pb.variables;
			if (num > 0) {
				Variable neighbor = variables[idOfACNeighbors[num - 1]];
				int limit = nbConsistentValuesOfACNeighbors[num - 1];
				int[] t = consistentValuesOfACNeighbors[num - 1];
				assert IntStream.range(1, limit).allMatch(i -> t[i - 1] < t[i]);

				Domain dom = neighbor.dom;
				for (int i = 0, neighborIndex = dom.first(); neighborIndex != -1; neighborIndex = dom.next(neighborIndex)) {
					while (i < limit && t[i] < neighborIndex)
						i++;
					assert (i == limit || t[i] > neighborIndex) == (Arrays.binarySearch(t, 0, limit, neighborIndex) < 0);
					if (i == limit || t[i] > neighborIndex)
						neighbor.dom.removeElementary(neighborIndex);
				}
				if (dom.size() == 0 || !rdac.go(false))
					return -1;
				Domain.setMarks(solver.pb.variables, solver.top);
			}

			Variable neighbor = variables[idOfACNeighbors[num]];
			int limit = nbConsistentValuesOfACNeighbors[num];
			int[] t = consistentValuesOfACNeighbors[num];
			Domain dom = neighbor.dom;
			for (int i = 0; i < limit; i++)
				if (dom.isPresent(t[i]))
					dom.removeElementary(t[i]);
			// partitionOfConstraints.init();

			return dom.size() > 0 && rdac.go(false) ? 1 : 0;
		}
	}

	public class DecomposerRDAC2 extends Decomposer {

		private RDAC rdac;

		private Variable var;

		private int a;

		private int k;

		private int nbConstraintsToBeViolated;

		private Constraint[] constraintsToBeViolated;

		private boolean active;

		public int getIndex() {
			return a;
		}

		public DecomposerRDAC2(SolverBacktrackDecomposing solver) {
			super(solver);
			Problem problem = solver.pb;
			this.rdac = (RDAC) solver.propagation;
			Kit.control(problem.variables[0].heuristicVal instanceof Aic);
			constraintsToBeViolated = new Constraint[problem.stuff.maxVarDegree()];
		}

		@Override
		public int getNbPieces() {
			return 1;
		}

		private int offset;

		private int getAicOf(Variable x) {
			int[] aic = rdac.aic[x.num];
			offset = Integer.MAX_VALUE;
			Domain dom = x.dom;
			int bestIndex = dom.first();
			for (int idx = dom.next(bestIndex); idx != -1; idx = dom.next(idx)) {
				if (aic[idx] < aic[bestIndex]) {
					bestIndex = idx;
					offset = aic[bestIndex] - aic[idx];
				} else
					offset = Math.min(offset, aic[idx] - aic[bestIndex]);
			}
			return bestIndex;
		}

		@Override
		public void initialize(Variable x) {
			assert !x.isAssigned() && rdac.control();

			this.var = x;
			this.active = false;

			if (x.dom.size() == 1)
				return;

			this.a = getAicOf(x);
			assert (a == x.heuristicVal.bestIndex());
			k = offset + 1;

			long[][][] minCosts = rdac.minCosts;

			nbConstraintsToBeViolated = 0;
			for (Constraint c : x.ctrs) {
				if (c.futvars.size() == 1)
					continue; // optim coreccte a priori
				int i = c.num, j = c.positionOf(x);
				assert ((CtrHard) c).seekFirstSupportWith(j, a) != (minCosts[i][j][a] > 0);
				if (minCosts[i][j][a] > 0)
					continue;
				// if (!constraint.seekConflict(j, index))
				// continue; // pas efficace

				constraintsToBeViolated[nbConstraintsToBeViolated++] = c;
			}
			// System.out.println("nb=" + nb + " nbConstraints=" + nbConstraints);
		}

		@Override
		public void split() {
			active = true;
		}

		@Override
		public int buildPiece(int num) {
			return 1;
		}

		public boolean isSatisfied() {
			if (!active)
				return true;
			int cnt = 0;
			for (int i = 0; cnt < k && i < nbConstraintsToBeViolated; i++)
				if (((CtrHard) constraintsToBeViolated[i]).seekFirstConflictWith(constraintsToBeViolated[i].positionOf(var), a)) {
					if (cnt < i)
						Kit.swap(constraintsToBeViolated, cnt, i);
					cnt++;
				}
			return cnt >= k;
		}
	}

}
