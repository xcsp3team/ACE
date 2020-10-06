/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/*
 * From http://jimorlin.wordpress.com/2009/02/17/colored-letters-labeled-dice-a-logic-puzzle/ There are 13 words as follows: BUOY, CAVE, CELT, FLUB, FORK, HEMP,
 * JUDY, JUNK, LIMN, QUIP, SWAG, VISA, WISH. There are 24 different letters that appear in the 13 words. The question is: can one assign the 24 letters to 4
 * different cubes so that the four letters of each word appears on different cubes. (There is one letter from each word on each cube.). The puzzle was created
 * by Humphrey Dudley
 */
public class LabeledDice implements ProblemAPI {

	@Override
	public void model() {
		String[] words = { "BUOY", "CAVE", "CELT", "FLUB", "FORK", "HEMP", "JUDY", "JUNK", "LIMN", "QUIP", "SWAG", "VISA" };
		int nCubes = 4;

		Var[] x = array("x", size(26), i -> Stream.of(words).anyMatch(w -> w.indexOf((char) ('A' + i)) != -1) ? dom(rangeClosed(1, nCubes)) : null,
				"x[i] is the cube where the ith letter of the alphabet is put");
		forall(range(words.length), i -> allDifferent((Var[]) variablesFrom(words[i].chars(), c -> x[c - 'A'])))
				.note("the four letters of each word appears on different cubes");
		cardinality(x, rangeClosed(1, nCubes), occursEachExactly(6)).note("each cube is assigned 6 letters");
	}
}
