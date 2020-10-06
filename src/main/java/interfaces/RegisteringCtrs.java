/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package interfaces;

import java.util.List;

import constraints.Constraint;
import variables.domains.Domain;

public interface RegisteringCtrs {

	/** The list of constraints registered by this object. */
	abstract List<Constraint> registeredCtrs();

	default void register(Constraint c) {
		assert !registeredCtrs().contains(c) && (registeredCtrs().size() == 0 || Domain.similarDomains(c.doms, firstRegisteredCtr().doms));
		registeredCtrs().add(c);
	}

	default void unregister(Constraint c) {
		boolean b = registeredCtrs().remove(c);
		assert b;
	}

	default Constraint firstRegisteredCtr() {
		return registeredCtrs().get(0);
	}
}
