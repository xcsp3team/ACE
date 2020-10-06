/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.Scanner;
import java.util.stream.IntStream;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.SchedulingFS;

public class SchedulingFSReader extends SchedulingFS implements ReaderTxt {

	// java org.xcsp.modeler.Compiler problems.generators.SchedulingFSReader\$Taillard /home/lecoutre/instances/scheduling/taillard/fs/fs-020-05.txt 1
	// -dataSaving
	public static class Taillard extends SchedulingFSReader {
		void data() {
			Scanner scanner = scanner();
			int num = imp().askInt("num", range(10));
			IntStream.rangeClosed(0, num).forEach(i -> scanner.findWithinHorizon("ower bound", 0));
			nextLine(); // to skip the rest of the line
			int n = nextInt(); // nJobs
			int m = nextInt(); // nOperations and nMachines
			nextLong(); // time seed, not used here
			nextInt(); // ub
			nextInt(); // lb
			nextLine();
			nextLine();
			int[][] durations = transpose(range(m).range(n).map((i, j) -> nextInt())); // transpose because not given in the same order
			setDataValues(durations);
		}
	}
}