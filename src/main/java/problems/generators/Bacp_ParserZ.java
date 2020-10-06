/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.Bacp;

public class Bacp_ParserZ extends Bacp implements ReaderDzn {

	void data() {
		nextLine();
		int nCourses = nextInt(), nPeriods = nextInt();
		int minCredits = nextInt(), maxCredits = nextInt();
		int minCourses = nextInt(), maxCourses = nextInt();
		int[] credits = nextInt1D();
		Utilities.control(nCourses == credits.length, "");
		String[] lines = nextLines();
		int[][] prerequisites = Stream.of(lines).map(line -> line.split("constraint prerequisite\\(|,|\\);"))
				.map(t -> tuple(Integer.parseInt(t[1].trim()) - 1, Integer.parseInt(t[2].trim()) - 1)).toArray(int[][]::new);
		setDataValues(nPeriods, minCredits, maxCredits, minCourses, maxCourses, credits, prerequisites);
	}
}
