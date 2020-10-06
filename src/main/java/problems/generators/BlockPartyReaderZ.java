/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderDzn;
import problems.todo.BlockParty;

public class BlockPartyReaderZ extends BlockParty implements ReaderDzn {

	void data() {
		int[][] data = nextInt2D();
		setDataValues(data);
	}
}
