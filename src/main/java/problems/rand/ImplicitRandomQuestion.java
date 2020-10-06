/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.rand;

/**
 * This class corresponds to implicit random problems, i.e., random problems such that constraints are defined by a predicate as described in: <br>
 * [Lecoutre, Boussemart et Hemery, 03, Implicit Random CSPs, ICTAI'03].
 */
public class ImplicitRandomQuestion extends ImplicitRandom {

	void data() {
		n = imp().askInt("nVariables");
		d = imp().askInt("domain size");
		e = imp().askInt("nConstraints");
		r = imp().askInt("arity");
		tightness = imp().askInt("Constraint tightness (an integer value between 1 and 255)", rangeClosed(1, 255));
		seed = imp().askInt("seed");
		macroType = imp().askInt("Constraint Graph Type \n  0 : unstructured \n 1 : connected \n 2 : balanced \nYour choice : ", range(3));
		repetition = imp().askBoolean("Possibility of generating several constraints with same signature (yes/no) : ");
		sat = imp().askBoolean("Generation of satisfiable instances (yes/no) : ");
		algorithm = imp().askString("algorithm");
	}

}
