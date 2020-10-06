/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;

/**
 * This is a Radar surveillance instance where " + nRadars + " radars must be put on a geographic area of size " + mapSize + "*" + mapSize + "." There
 * are " + nInsignificantCells + " insignificant cells that must not be covered by any radar. All other cells must be covered by exactly " +
 * maxCoverage + " radars." + " This instance has been generated using a seed equal to " + seed . This instance follows the description given by the
 * Swedish Institute of Computer Science (SICS).
 * 
 */
public class RadarSurveillance implements ProblemAPI {

	int mapSize;
	int maxCoverage;
	int[][] radars;
	int[][] insignificantCells;

	static enum Sector {
		NEAST, // north east
		EAST,
		SEAST, // south east
		SWEST, // south west
		WEST,
		NWEST; // north west

		int rowOfNextRightCell(int iCell) {
			return iCell + (this == NEAST || this == NWEST ? -1 : this == EAST || this == WEST ? 0 : 1);
		}

		int rowOfNextLeftCell(int iCell) {
			return iCell + (this == NEAST || this == EAST ? -1 : this == SEAST || this == NWEST ? 0 : 1);
		}

		int colOfNextRightCell(int iCell, int jCell) {
			boolean oddRow = (iCell % 2 == 1);
			return jCell + (this == EAST ? 1 : this == WEST ? -1 : this == NEAST || this == SEAST ? (oddRow ? 0 : 1) : -(oddRow ? 1 : 0));
		}

		int colOfNextLeftCell(int iCell, int jCell) {
			boolean oddRow = (iCell % 2 == 1);
			return jCell + (this == SEAST ? 1 : this == NWEST ? -1 : this == EAST || this == SWEST ? (oddRow ? 0 : 1) : -(oddRow ? 1 : 0));
		}
	}

	private int distance(int iCell, int jCell, int iCurr, int jCurr, Sector sector, int currDistance, int maxDistance) {
		if (currDistance > maxDistance)
			return -1;
		if (iCell == iCurr && jCell == jCurr)
			return currDistance;
		int distance = distance(iCell, jCell, sector.rowOfNextRightCell(iCurr), sector.colOfNextRightCell(iCurr, jCurr), sector, currDistance + 1, maxDistance);
		if (distance != -1)
			return distance;
		return distance(iCell, jCell, sector.rowOfNextLeftCell(iCurr), sector.colOfNextLeftCell(iCurr, jCurr), sector, currDistance + 1, maxDistance);
	}

	private boolean isInsignificant(int iCell, int jCell) {
		return Stream.of(insignificantCells).anyMatch(t -> t[0] == iCell && t[1] == jCell);
	}

	private CtrEntity dealWithCell(Var[][] x, int iCell, int jCell, int maximumDistance) {
		List<Var> vars = new ArrayList<>();
		List<Integer> dists = new ArrayList<>();
		for (int i = 0; i < radars.length; i++)
			for (Sector sector : Sector.values()) {
				int distance = distance(iCell, jCell, sector.rowOfNextRightCell(radars[i][0]), sector.colOfNextRightCell(radars[i][0], radars[i][1]), sector, 1,
						maximumDistance);
				if (distance != -1) {
					vars.add(x[i][sector.ordinal()]);
					dists.add(distance);
				}
			}
		if (vars.size() == 0)
			return null;
		if (vars.size() == 1)
			return isInsignificant(iCell, jCell) ? lessThan(vars.get(0), dists.get(0)) : greaterThan(vars.get(0), dists.get(0) - 1);
		// XNodeParent<>[] args = IntStream.range(0, vars.size()).mapToObj(i -> ge(vars.get(i), dists.get(i))).toArray();
		// return sum(args,EQ, equal(add(args), isInsignificant(iCell, jCell) ? 0 : Math.min(vars.size(), maxCoverage));
		return sum(treesFrom(IntStream.range(0, vars.size()), i -> ge(vars.get(i), dists.get(i))), EQ,
				isInsignificant(iCell, jCell) ? 0 : Math.min(vars.size(), maxCoverage));
	}

	@Override
	public void model() {
		int nRadars = radars.length, nSectors = Sector.values().length;

		Var[][] x = array("x", size(nRadars, nSectors), dom(range(maxCoverage + 1)), "x[i][j] is the power of the ith radar in the jth sector");
		forall(range(mapSize).range(mapSize), (i, j) -> dealWithCell(x, i, j, maxCoverage));
	}

}