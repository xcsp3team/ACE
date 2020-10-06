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
import problems.g3_pattern.OpenStacks;

// java abscon.Resolution problems.patt.OpenStacks -model=m2 problem_15_15_1.dzn -f=cop -os=decreasing -sing=Last -varh=Impact =>optimum 7 in 98s
public class OpenStacks_ParserZ extends OpenStacks implements ReaderDzn {

	void data() {
		nextInt(); // n
		nextInt(); // m
		int[][] orders = nextInt2D();
		setDataValues(orders);
	}

}
