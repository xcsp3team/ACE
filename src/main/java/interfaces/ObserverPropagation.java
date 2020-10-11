/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package interfaces;

import constraints.Constraint;
import variables.Variable;

public interface ObserverPropagation {
	// public void afterAssignment(Variable x, int a);
	//
	// public void afterUnassignment(Variable x);

	public void whenWipeout(Constraint c, Variable x);

	// public void whenReduction(Constraint c, Variable x);
}
