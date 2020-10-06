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

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.SchedulingOS;

public class SchedulingOSReader extends SchedulingOS implements ReaderTxt {

	public static class Gp extends SchedulingOSReader {
		void data() {
			nextLine(); // to skip the first line
			int m = nextInt(); // nbMachines
			int n = nextInt(); // nbJobs
			int[][] durations = transpose(range(m).range(n).map((i, j) -> nextInt())); // transpose because not given in the same order as
			// js and os
			// ub = 1400; // hard limit, see ub in readme.txt of os-gp
			setDataValues(durations);
		}
	}

	public static class Taillard extends SchedulingOSReader {
		void data() {
			Scanner scanner = scanner();
			int num = imp().askInt("num", range(10));
			IntStream.rangeClosed(0, num).forEach(i -> scanner.findWithinHorizon("ower bound", 0));
			nextLine(); // to skip the rest of the line
			int n = nextInt(); // nJobs
			int m = nextInt(); // nOperations and nMachines
			nextLong(); // time seed, not used here
			nextLong(); // machine seed
			nextInt(); // ub
			nextInt(); // lb
			nextLine();
			nextLine();
			int[][] durations1 = range(n).range(m).map((i, j) -> nextInt());
			nextLine();
			nextLine();
			int[][] resources = range(n).range(m).map((i, j) -> nextInt() - 1); // -1 for starting machine id at 0
			int[][] durations = range(n).range(m).map((i, j) -> durations1[i][Utilities.indexOf(j, resources[i])]); // we have to reorder times for os
			// because they are given according to the order of machines
			setDataValues(durations);
			scanner.close();
		}
	}
}