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
import java.util.stream.Stream;

import org.xcsp.common.Utilities;
import org.xcsp.modeler.problems.Blackhole;

import problems.ReaderFile.ReaderDzn;
import utility.Kit;

public class BlackholeReaderZ extends Blackhole implements ReaderDzn {

	void data() {
		Scanner in = imp().fileScanner();
		in.nextLine();
		int[][] m = IntStream.range(0, 17).mapToObj(i -> Utilities.splitToInts(in.nextLine(), ",|\\s")).toArray(int[][]::new);
		Stream.of(m).forEach(t -> IntStream.range(0, t.length).forEach(i -> t[i]--));
		System.out.println("Line" + Kit.join(m));
		// int[][] shifts = nextInt2Dc();
		setDataValues(13, 3, m);
	}
}