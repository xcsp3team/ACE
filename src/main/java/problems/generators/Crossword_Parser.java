/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.io.File;
import java.io.IOException;
import java.util.Scanner;

import org.xcsp.common.Utilities;

import problems.ReaderFile;
import problems.g4_world.Crossword;
import utility.Kit;

public class Crossword_Parser extends Crossword implements ReaderFile {

	void data() {
		String gridFileName = imp().askString("Grid file name");
		String dictFileName = imp().askString("Dict file name");
		int[][] spots = null;
		if (gridFileName.startsWith("vg")) {
			int[] t = Utilities.splitToInts(gridFileName, "vg|-");
			spots = new int[t[0]][t[1]];
		} else {
			try (Scanner in = new Scanner(new File(gridFileName))) {
				int[] t = Utilities.splitToInts(in.nextLine().trim(), "\\(\\s*|\\s*x\\s*|\\s*\\)");
				spots = new int[t[0]][t[1]];
				for (int i = 0; i < t[0]; i++) {
					String[] tokens = in.nextLine().trim().split("\\(|\\)|\\s+");
					for (int j = 0; j < t[1]; j++)
						spots[i][j] = tokens[j + 1].charAt(0) == '*' ? 1 : 0;
				}
			} catch (IOException e) {
				Kit.exit(e);
			}
		}
		setDataValues(spots, dictFileName);
	}

}
