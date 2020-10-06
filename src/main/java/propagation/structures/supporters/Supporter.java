/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.supporters;

import constraints.Constraint;

public abstract class Supporter<T extends Constraint> {
	protected T c;

	protected boolean multidirectionality;

	protected int[] buffer;

	public Supporter(T c) {
		this.c = c;
		this.multidirectionality = c.pb.rs.cp.propagating.multidirectionality;
		this.buffer = c.tupleManager.localTuple;
	}
}