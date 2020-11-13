/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.intension;

import java.util.stream.Stream;

import constraints.Constraint;
import interfaces.FilteringSpecific;
import interfaces.TagFilteringCompleteAtEachCall;
import problem.Problem;
import variables.Variable;

public abstract class Primitive extends Constraint implements FilteringSpecific, TagFilteringCompleteAtEachCall {

	protected final void defineKey(Object... datas) {
		StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
		Stream.of(datas).forEach(data -> sb.append(' ').append(data.toString()));
		this.key = sb.toString();
	}

	public Primitive(Problem pb, Variable[] scp) {
		super(pb, scp);
		defineKey(); // most of the time, no specific data (otherwise, call it again in subclasses with the right args)
	}
}
