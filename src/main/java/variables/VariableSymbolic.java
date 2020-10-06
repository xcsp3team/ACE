/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables;

import org.xcsp.common.IVar;

import problem.Problem;
import problem.Symbolic;
import variables.domains.DomainInteger.DomainSymbols;

/**
 * This class gives the description of a symbolic variable. <br>
 */
public class VariableSymbolic extends Variable implements IVar.VarSymbolic {

	/**
	 * Builds a variable with a domain composed of all specified symbolic values.
	 */
	public VariableSymbolic(Problem problem, String name, String[] symbols) {
		super(problem, name);
		if (problem.symbolic == null)
			problem.symbolic = new Symbolic();
		int[] values = problem.symbolic.manageSymbols(symbols); // values associated with symbols
		this.dom = new DomainSymbols(this, values, symbols);
	}
}
