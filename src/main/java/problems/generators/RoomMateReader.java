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

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.RoomMate;

public class RoomMateReader extends RoomMate implements ReaderTxt {

	void data() {
		int n = Integer.parseInt(nextLine());
		int[][] preferences = range(n).mapToObj(i -> Utilities.splitToInts(nextLine()));
		setDataValues(preferences);
	}

}
