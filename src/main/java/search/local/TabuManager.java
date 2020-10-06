/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package search.local;

import variables.Variable;

public abstract class TabuManager {

	public abstract void push(Variable x, int a);

	public abstract boolean isTabu(Variable x, int a);

	public static class TabuManagerVariable extends TabuManager {

		private boolean[] tabus;

		private int[] t1;

		private int head;

		public TabuManagerVariable(SolverLocal solver, int tabuListSize) {
			if (tabuListSize > 0) {
				this.tabus = new boolean[solver.pb.variables.length];
				this.t1 = new int[tabuListSize];
			}
		}

		@Override
		public void push(Variable x, int a) {
			if (!tabus[x.num]) {
				tabus[t1[head]] = false;
				tabus[x.num] = true;
				t1[head] = x.num;
				head = (head + 1) % t1.length;
			}
		}

		@Override
		public boolean isTabu(Variable x, int a) {
			return tabus != null && tabus[x.num];
		}

	}

	public static class TabuManagerVariableValue extends TabuManager {

		private boolean[][] tabus;

		private int[] t1, t2;

		private int head;

		public TabuManagerVariableValue(SolverLocal solver, int tabuListSize) {
			if (tabuListSize > 0) {
				this.tabus = Variable.litterals(solver.pb.variables).booleanArray();
				this.t1 = new int[tabuListSize];
				this.t2 = new int[tabuListSize];
			}
		}

		@Override
		public void push(Variable x, int a) {
			// assert tabus[variable.getId()][index] != true : variable + " " + index + " already tabu";
			if (!tabus[x.num][a]) {
				tabus[t1[head]][t2[head]] = false;
				tabus[x.num][a] = true;
				t1[head] = x.num;
				t2[head] = a;
				head = (head + 1) % t1.length;
			}
		}

		@Override
		public boolean isTabu(Variable x, int a) {
			return tabus != null && tabus[x.num][a];
		}
	}

}
