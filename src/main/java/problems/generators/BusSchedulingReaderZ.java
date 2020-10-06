/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderDzn;
import problems.g3_pattern.BusScheduling;

public class BusSchedulingReaderZ extends BusScheduling implements ReaderDzn {

	void data() {
		int nTasks = nextInt();
		int nShifts = nextInt();
		nextInt();
		int[][] shifts = nextInt2Dc();
		Utilities.control(nShifts == shifts.length, "");
		setDataValues(nTasks, (Object) shifts);
	}
}