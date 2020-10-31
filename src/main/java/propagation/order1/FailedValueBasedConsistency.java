/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.order1;

import java.util.ArrayList;
import java.util.List;

import constraints.Constraint;
import interfaces.ObserverConstruction;
import search.backtrack.DecisionRecorder;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class FailedValueBasedConsistency implements ObserverConstruction {

	protected AC arcConsistency;

	public int nInferredBacktracks;

	public int nInferredRemovals;

	public FailedValueBasedConsistency(AC arcConsistency) {
		this.arcConsistency = arcConsistency;
		arcConsistency.solver.rs.observersConstruction.add(this);
	}

	public abstract boolean enforce();

	// ************************************************************************
	// Subclass FailedValueConsistency
	// ************************************************************************

	public static class FailedValueConsistency extends FailedValueBasedConsistency {

		private static final int CONFLICT_SEEKING_LIMIT = 1000;

		private Constraint[][] residues;

		@Override
		public void onConstructionSolverFinished() {
			Variable[] variables = arcConsistency.solver.pb.variables;
			residues = new Constraint[variables.length][];
			for (int i = 0; i < residues.length; i++) {
				residues[i] = new Constraint[variables[i].dom.initSize()];
				for (int j = 0; j < residues[i].length; j++)
					residues[i][j] = variables[i].ctrs[0]; // so as to never have residues as being null
			}
		}

		public FailedValueConsistency(AC arcConsistency) {
			super(arcConsistency);
		}

		private Constraint seekConflictingConstraintFor(Variable x, int a) {
			Constraint residue = residues[x.num][a];
			int p = residue.positionOf(x);
			if (Variable.nValidTuplesBoundedAtMaxValueFor(residue.scp, p) > CONFLICT_SEEKING_LIMIT || residue.seekFirstConflictWith(p, a))
				return residue;
			for (Constraint c : x.ctrs) {
				if (c == residue)
					continue;
				p = c.positionOf(x);
				if (Variable.nValidTuplesBoundedAtMaxValueFor(c.scp, p) > CONFLICT_SEEKING_LIMIT || c.seekFirstConflictWith(p, a))
					return c;
			}
			return null;
		}

		@Override
		public boolean enforce() {
			DecisionRecorder dr = ((SolverBacktrack) arcConsistency.solver).dr;
			for (int i = dr.decisions.limit; i >= 0; i--) {
				int d = dr.decisions.dense[i];
				if (d > 0 || dr.isFailedAssignment(i))
					continue;
				Variable x = dr.varIn(d);
				int a = dr.idxIn(d);
				Constraint c = seekConflictingConstraintFor(x, a);
				if (c == null) {
					nInferredBacktracks++;
					return false;
				} else
					residues[x.num][a] = c;
			}
			return true;
		}
	}

	// ************************************************************************
	// Subclass PartialArcFailedValueConsistency
	// ************************************************************************

	public static class PartialArcFailedValueConsistency extends FailedValueBasedConsistency {

		private static final int CONFLICT_SEEKING_LIMIT = 1000;

		@Override
		public void onConstructionSolverFinished() {}

		public PartialArcFailedValueConsistency(AC arcConsistency) {
			super(arcConsistency);
		}

		private Constraint seekUniqueConflictingConstraintFor(Variable x, int a) {
			Constraint ctr = null;
			for (Constraint c : x.ctrs) {
				int p = c.positionOf(x);
				if (Variable.nValidTuplesBoundedAtMaxValueFor(c.scp, p) > CONFLICT_SEEKING_LIMIT)
					return Constraint.TAG;
				if (c.seekFirstConflictWith(p, a)) {
					if (ctr == null && c.scp.length == 2 && c.scp[p == 1 ? 0 : 1].dom.size() > 1)
						ctr = c;
					else
						return Constraint.TAG;
				}
			}
			return ctr;
		}

		@Override
		public boolean enforce() {
			assert arcConsistency.queue.size() == 0;
			DecisionRecorder dr = ((SolverBacktrack) arcConsistency.solver).dr;
			for (int i = dr.decisions.limit; i >= 0; i++) {
				int d = dr.decisions.dense[i];
				if (d > 0 || dr.isFailedAssignment(i))
					continue;
				Variable x = dr.varIn(d);
				int a = dr.idxIn(d);
				Constraint c = seekUniqueConflictingConstraintFor(x, a);
				if (c == null) {
					nInferredBacktracks++;
					return false;
				} else if (c != Constraint.TAG) {
					assert c.scp.length == 2;
					int p = c.positionOf(x), q = p == 0 ? 1 : 0;
					Variable y = c.scp[q];
					Domain domy = y.dom;
					int sizeBefore = domy.size();
					for (int b = domy.first(); b != -1; b = domy.next(b))
						if (c.seekFirstSupportWith(p, a, q, b))
							y.dom.removeElementary(b);
					int nRemovals = (sizeBefore - domy.size());
					if (nRemovals > 0) {
						nInferredRemovals += nRemovals;
						if (domy.size() == 0)
							return false;
						if (!arcConsistency.runAfterRefutation(y))
							return false;
					}
				}
			}
			return true;
		}
	}

	// ************************************************************************
	// Subclass ArcFailedValueConsistency
	// ************************************************************************

	public static class ArcFailedValueConsistency extends FailedValueBasedConsistency {

		private void updateConflictsList(Constraint c) {
			assert c.scp.length == 2;
			Variable x = c.scp[0], y = c.scp[1];
			int[] tuple = c.tupleManager.localTuple;
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				tuple[0] = a;
				for (int b = y.dom.first(); b != -1; b = y.dom.next(b)) {
					tuple[1] = b;
					if (!c.checkIndexes(tuple)) {
						conflictsVariableList[x.num][a].add(y);
						conflictsIndexList[x.num][a].add(b);
						conflictsVariableList[y.num][b].add(x);
						conflictsIndexList[y.num][b].add(a);
					}
				}
			}
		}

		@Override
		public void onConstructionSolverFinished() {
			Kit.control(arcConsistency.solver.pb.stuff.minCtrArity() == 2 && arcConsistency.solver.pb.stuff.maxCtrArity() == 2);

			Variable[] variables = arcConsistency.solver.pb.variables;
			Constraint[] constraints = arcConsistency.solver.pb.constraints;

			conflictsVariableList = new List[variables.length][];
			conflictsIndexList = new List[variables.length][];
			for (int i = 0; i < variables.length; i++) {
				Domain dom = variables[i].dom;
				conflictsVariableList[i] = new List[dom.initSize()];
				conflictsIndexList[i] = new List[dom.initSize()];
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					conflictsVariableList[i][a] = new ArrayList<>();
					conflictsIndexList[i][a] = new ArrayList<>();
				}
			}

			for (Constraint ctr : constraints)
				updateConflictsList(ctr);

			conflictsVariable = new Variable[variables.length][][];
			conflictsIndex = new int[variables.length][][];
			residuesVariable = new Variable[variables.length][][][];
			residuesIndex = new int[variables.length][][][];

			for (int i = 0; i < variables.length; i++) {
				Domain dom = variables[i].dom;
				conflictsVariable[i] = new Variable[dom.initSize()][];
				conflictsIndex[i] = new int[dom.initSize()][];
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					conflictsVariable[i][a] = conflictsVariableList[i][a].toArray(new Variable[0]);
					List<Integer> list = conflictsIndexList[i][a];
					conflictsIndex[i][a] = Kit.intArray(list);
				}
				residuesVariable[i] = new Variable[dom.initSize()][variables.length][];
				residuesIndex[i] = new int[dom.initSize()][variables.length][];
				for (int j = 0; j < residuesVariable[i].length; j++)
					for (int k = 0; k < residuesVariable[i][j].length; k++) {
						residuesVariable[i][j][k] = new Variable[variables[k].dom.initSize()];
						residuesIndex[i][j][k] = new int[variables[k].dom.initSize()];
					}
			}

			binaryConstraints = new Constraint[variables.length][variables.length];
			for (Constraint c : constraints) {
				Variable x = c.scp[0], y = c.scp[1];
				binaryConstraints[x.num][y.num] = c;
				binaryConstraints[y.num][x.num] = c;
			}
			// displayConflictsLists();
		}

		private Variable[][][] conflictsVariable; // 1D = variable index; 2D=index; 3D =order

		private int[][][] conflictsIndex;

		private Variable[][][][] residuesVariable; // 1+2D = v-value=pivot, 3+4D= v-value

		private int[][][][] residuesIndex;

		private Constraint[][] binaryConstraints; // 1D = variable id , 2D=variale ID

		private List<Variable>[][] conflictsVariableList; // 1D = variable index; 2D=index; 3D =order

		private List<Integer>[][] conflictsIndexList;

		private int[] tuple = new int[2];

		public ArcFailedValueConsistency(AC arcConsistency) {
			super(arcConsistency);
		}

		@Override
		public boolean enforce() {
			DecisionRecorder dr = ((SolverBacktrack) arcConsistency.solver).dr;
			for (int i = dr.decisions.limit; i >= 0; i--) {
				int d = dr.decisions.dense[i];
				if (d > 0 || dr.isFailedAssignment(i))
					continue;
				Variable varPivot = dr.varIn(d);
				int idxPivot = dr.idxIn(d);

				Variable[] convar = conflictsVariable[varPivot.num][idxPivot];
				int[] conind = conflictsIndex[varPivot.num][idxPivot];

				Variable[][] resvar = residuesVariable[varPivot.num][idxPivot];
				int[][] resind = residuesIndex[varPivot.num][idxPivot];

				for (Variable x = arcConsistency.solver.futVars.first(); x != null; x = arcConsistency.solver.futVars.next(x)) {
					Variable[] resvar2 = resvar[x.num];
					int[] resind2 = resind[x.num];

					Domain domx = x.dom;
					int sizeBefore = domx.size();
					for (int a = domx.first(); a != -1; a = domx.next(a)) {
						if (resvar2[a] != null && resvar2[a].dom.isPresent(resind2[a]))
							continue;
						boolean found = false;
						for (int j = 0; !found && j < convar.length; j++) {
							if (!convar[j].dom.isPresent(conind[j]))
								continue;

							Constraint binaryConstraint = binaryConstraints[convar[j].num][x.num];
							if (binaryConstraint == null) {
								resvar2[a] = convar[j];
								resind2[a] = conind[j];
								found = true;
							} else {
								if (binaryConstraint.scp[0] == x) {
									tuple[0] = a;
									tuple[1] = conind[j];
								} else {
									tuple[0] = conind[j];
									tuple[1] = a;
								}
								if (binaryConstraint.checkIndexes(tuple)) {
									resvar2[a] = convar[j];
									resind2[a] = conind[j];
									found = true;
								}
							}
						}
						if (!found)
							domx.removeElementary(a);
					}

					if (sizeBefore != domx.size()) {
						this.nInferredRemovals += sizeBefore - domx.size();
						if (domx.size() == 0)
							return false;
						arcConsistency.queue.add(x);
					}
				}
			}
			return arcConsistency.propagate(); // true;
		}

		// public void displayConflictsLists() {
		// Variable[] variables = arcConsistency.solver.pb.variables;
		// for (int i = 0; i < variables.length; i++) {
		// Domain dom = variables[i].dom;
		// for (int idx = dom.first(); idx != -1; idx = dom.next(idx)) {
		// System.out.print(variables[i] + "=" + idx + ":: ");
		// for (int j = 0; j < conflictsVariable[i][idx].length; j++)
		// System.out.print(conflictsVariable[i][idx][j] + "=" + conflictsIndex[i][idx][j] + " ");
		// System.out.println();
		// }
		// }
		// }
	}

}
