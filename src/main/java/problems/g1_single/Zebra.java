/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g1_single;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// 48 solutions
public class Zebra implements ProblemAPI {

	@Override
	public void model() {
		Var yellow = var("yellow", dom(rangeClosed(1, 5)));
		Var green = var("green", dom(rangeClosed(1, 5)));
		Var red = var("red", dom(rangeClosed(1, 5)));
		Var white = var("white", dom(rangeClosed(1, 5)));
		Var blue = var("blue", dom(rangeClosed(1, 5)));

		Var italy = var("italy", dom(rangeClosed(1, 5)));
		Var spain = var("spain", dom(rangeClosed(1, 5)));
		Var japan = var("japan", dom(rangeClosed(1, 5)));
		Var england = var("england", dom(rangeClosed(1, 5)));
		Var norway = var("norway", dom(rangeClosed(1, 5)));

		Var painter = var("painter", dom(rangeClosed(1, 5)));
		Var sculptor = var("sculptor", dom(rangeClosed(1, 5)));
		Var diplomat = var("diplomat", dom(rangeClosed(1, 5)));
		Var pianist = var("pianist", dom(rangeClosed(1, 5)));
		Var doctor = var("doctor", dom(rangeClosed(1, 5)));

		Var cat = var("cat", dom(rangeClosed(1, 5)));
		Var zebra = var("zebra", dom(rangeClosed(1, 5)));
		Var bear = var("bear", dom(rangeClosed(1, 5)));
		Var snails = var("snails", dom(rangeClosed(1, 5)));
		Var horse = var("horse", dom(rangeClosed(1, 5)));

		Var milk = var("milk", dom(rangeClosed(1, 5)));
		Var water = var("water", dom(rangeClosed(1, 5)));
		Var tea = var("tea", dom(rangeClosed(1, 5)));
		Var coffee = var("coffee", dom(rangeClosed(1, 5)));
		Var juice = var("juice", dom(rangeClosed(1, 5)));

		allDifferent(yellow, green, red, white, blue);
		allDifferent(italy, spain, japan, england, norway);
		allDifferent(painter, sculptor, diplomat, pianist, doctor);
		allDifferent(cat, zebra, bear, snails, horse);
		allDifferent(milk, water, tea, coffee, juice);

		equal(painter, horse);
		equal(diplomat, coffee);
		equal(white, milk);
		equal(spain, painter);
		equal(england, red);
		equal(snails, sculptor);
		equal(add(green, 1), red);
		equal(add(blue, 1), norway);
		equal(doctor, milk);
		equal(japan, diplomat);
		equal(norway, zebra);
		equal(dist(green, white), 1);
		belong(horse, set(sub(diplomat, 1), add(diplomat, 1)));
		belong(italy, set(red, white, green));
	}
}
