/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import utility.Bit;
import utility.Kit;

public class State {

	public final int[] vids;

	private long[][] domainRepresentations;

	private int watchedVariablePosition0 = -1;

	private int watchedVariablePosition1 = -1;

	private int watchedIndex0 = -1;

	private int watchedIndex1 = -1;

	public int getVariableIdWatchedAt(int watchPosition) {
		return vids[watchPosition == 0 ? watchedVariablePosition0 : watchedVariablePosition1];
	}

	public int getVariablePositionAt(int watchPosition) {
		return watchPosition == 0 ? watchedVariablePosition0 : watchedVariablePosition1;
	}

	// public int getVariablePositionNotAt(int watchPosition) {
	// return watchPosition == 1 ? watchedVariablePosition0 : watchedVariablePosition1;
	// }

	public int getIndexWatchedAt(int watchPosition) {
		return watchPosition == 0 ? watchedIndex0 : watchedIndex1;
	}

	public long[] getDomainRepresentationOfVariableAtPosition(int position) {
		return domainRepresentations[position];
	}

	public int getFirstAbsentIndexFor(int pos) {
		return Bit.firstZeroIn(domainRepresentations[pos]);
	}

	public boolean isWatched(int variableId) {
		return vids[watchedVariablePosition0] == variableId || vids[watchedVariablePosition1] == variableId;
	}

	public int getWatchPositionOf(int variableId) {
		// assert isWatched(variableId);
		return (vids[watchedVariablePosition0] == variableId ? 0 : 1);
	}

	public int getVariableIdOfWatchDifferentFrom(int variableId) {
		assert isWatched(variableId);
		return (vids[watchedVariablePosition0] == variableId ? vids[watchedVariablePosition1] : vids[watchedVariablePosition0]);
	}

	public long[] getDomainRepresentationOfWatchedVariable(int variableId) {
		assert isWatched(variableId);
		int position = (vids[watchedVariablePosition0] == variableId ? watchedVariablePosition0 : watchedVariablePosition1);
		return domainRepresentations[position];
	}

	public long[] getDomainRepresentationAt(int position) {
		return domainRepresentations[position];
	}

	public long[] getDomainRepresentationOfWatchedVariableAt(int watchPosition) {
		return domainRepresentations[watchPosition == 0 ? watchedVariablePosition0 : watchedVariablePosition1];
	}

	public void setVariablePosition(int watchPosition, int pos) {
		if (watchPosition == 0)
			watchedVariablePosition0 = pos;
		else
			watchedVariablePosition1 = pos;
	}

	public void setIndex(int watchPosition, int indexPosition) {
		if (watchPosition == 0)
			watchedIndex0 = indexPosition;
		else
			watchedIndex1 = indexPosition;
	}

	public void setWatch(int watchPosition, int pos, int indexPosition) {
		if (watchPosition == 0) {
			watchedVariablePosition0 = pos;
			watchedIndex0 = indexPosition;
		} else {
			watchedVariablePosition1 = pos;
			watchedIndex1 = indexPosition;
		}
	}

	public State(LearnerStatesDominance stateDominanceManager, int[] variableIndices) {
		this.vids = variableIndices;
		this.domainRepresentations = new long[variableIndices.length][];
		for (int i = 0; i < domainRepresentations.length; i++)
			domainRepresentations[i] = stateDominanceManager.solver.problem.variables[variableIndices[i]].dom.binaryRepresentation().clone();
		stateDominanceManager.nGeneratedHyperNogoods++;
		// System.out.println(this);
		// DotSaver.setVariableIndices(variableIndices);
		// DotSaver.saveGraph(solver.problem);
	}

	private State(LearnerStatesDominance stateDominanceManager, State hn, boolean[] proof) {
		int cnt = Kit.countIn(true,proof);
		vids = new int[cnt];
		domainRepresentations = new long[cnt][];
		cnt = 0;
		for (int i = 0; i < proof.length; i++) {
			if (proof[i]) {
				vids[cnt] = i;
				domainRepresentations[cnt] = stateDominanceManager.solver.problem.variables[i].dom.binaryRepresentation().clone();
				// domainRepresentations[cnt] = solver != null ?
				// solver.problem.getVariable(i).domain.getElements().getBinaryRepresentation().clone() :
				// hn.domainRepresentations[i];
				cnt++;
			}
		}
		stateDominanceManager.nGeneratedHyperNogoods++;
		// System.out.println(this);
	}

	public State(LearnerStatesDominance stateDominanceManager, boolean[] proof) {
		this(stateDominanceManager, null, proof);
	}

	public State(State hn, boolean[] proof) {
		this(null, hn, proof);
	}

	public boolean equals(Object o) {
		State hn = (State) o;
		if (vids.length != hn.vids.length)
			return false;
		for (int i = 0; i < vids.length; i++)
			if (vids[i] != hn.vids[i])
				return false;
		for (int i = 0; i < domainRepresentations.length; i++)
			for (int j = 0; j < domainRepresentations[i].length; j++)
				if (domainRepresentations[i][j] != hn.domainRepresentations[i][j])
					return false;
		return true;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder().append("IPS of size " + vids.length + " with watch1 = " + watchedVariablePosition0 + " and watch2 = "
				+ watchedVariablePosition1 + "\n");
		for (int i = 0; i < vids.length; i++)
			sb.append(vids[i] + " : " + Bit.decrypt(domainRepresentations[i]) + " \n");
		return sb.append("end\n").toString();
	}
}
