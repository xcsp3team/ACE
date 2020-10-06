/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package variables;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;

import problem.Problem;
import variables.domains.Domain;
import variables.domains.DomainBinary;
import variables.domains.DomainHugeInfinite;
import variables.domains.DomainInteger.DomainRange;
import variables.domains.DomainInteger.DomainValues;

/**
 * This class gives the description of an integer variable. <br>
 */
public class VariableInteger extends Variable implements IVar.Var {

	/**
	 * Builds a variable with a domain composed of all specified integer values. A range can be specified by giving an array of values composed of
	 * three int, the last one being the special value Domain.TAG_RANGE
	 */
	public VariableInteger(Problem problem, String name, int[] values) {
		super(problem, name);
		if (values.length == 1)
			this.dom = new DomainRange(this, values[0], values[0]);
		else if (values.length == 2)
			this.dom = new DomainBinary(this, values[0], values[1]);
		else if (values.length == 3 && values[2] == Domain.TAG_RANGE)
			this.dom = new DomainRange(this, values[0], values[1]);
		else
			this.dom = new DomainValues(this, values);
	}

	public VariableInteger(Problem problem, String name, int min, int max) {
		super(problem, name);
		if (min == Constants.MINUS_INFINITY_INT && max == Constants.PLUS_INFINITY_INT)
			this.dom = new DomainHugeInfinite(this, min, max);
		// else if (max - min > 20000)
		// this.dom = new DomainHugeBounded(this, min, max);
		else
			this.dom = new DomainRange(this, min, max);
	}

	@Override
	public Object allValues() {
		return dom.allValues();
	}

}
