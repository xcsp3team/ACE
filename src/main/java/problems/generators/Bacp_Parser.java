/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.HashMap;
import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Bacp;

public class Bacp_Parser extends Bacp implements ReaderTxt {
	void data() {
		boolean original = false; // hard coding
		// original at true means the original data files bacp08, bacp10 and bacp12. Otherwise, means files by Pierre
		if (original) {
			int[] t = Stream.of(nextLine().split("\\s+")).mapToInt(s -> Integer.parseInt(s)).toArray();
			// nPeriods, minLoad, maxLoad, minCourses, maxCourses
			Map<String, Integer> mapForCourses = new HashMap<>();
			String[] courses = nextLine().split("\\s+");
			IntStream.range(0, courses.length).forEach(i -> mapForCourses.put(courses[i], i));
			int[] credits = Stream.of(nextLine().split("\\s+")).mapToInt(s -> Integer.parseInt(s)).toArray();
			String[] pairs = nextLine().split("\\s+");
			int[][] prerequisites = range(pairs.length / 2).range(2).map((i, j) -> mapForCourses.get(pairs[i * 2 + j]));
			setDataValues(t[0], t[1], t[2], t[3], t[4], credits, prerequisites);
		} else {
			int nCourses = nextInt(), nPeriods = nextInt();
			int minCredits = nextInt(), maxCredits = nextInt();
			int nPrerequisites = nextInt();
			int[] credits = range(nCourses).map(i -> nextInt());
			int[][] prerequisites = range(nPrerequisites).range(2).map((i, j) -> nextInt());
			setDataValues(nPeriods, minCredits, maxCredits, 5, 7, credits, prerequisites); // 5 to 7 courses in each period
		}
	}
}
