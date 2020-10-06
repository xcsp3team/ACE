/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.Stream;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Auction;

public class Auction_Parser extends Auction implements ReaderTxt {

	void data() {
		nextInt(); // nItems
		nextInt(); // nBids
		nextLine();
		Stream<Object> bids = Stream.of(nextLines()).map(line -> line.split("\\s+"))
				.map(t -> buildInternClassObject("Bid", t[0], Stream.of(t).skip(1).mapToInt(v -> Integer.parseInt(v)).toArray()));
		setDataValues(bids);
	}
}
