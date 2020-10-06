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
import problems.g3_pattern.PrizeCollecting;

//java abscon.Resolution problems.generators.PrizeCollectingReaderZ ~/instances/minizinc-benchmarks-master/prize-collecting/15-3-5-0.dzn  -f=cop -varh=Memory -os=decreasing => 20 in 2646 wrong
public class PrizeCollecting_ParserZ extends PrizeCollecting implements ReaderDzn {

	void data() {
		int n = nextInt();
		int[][] prizes = nextInt2Db();
		setDataValues(n, (Object) prizes);
	}
}