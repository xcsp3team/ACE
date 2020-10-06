/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.hard.primitive;

import problem.Problem;
import variables.Variable;
import variables.domains.Domain;

public abstract class CtrPrimitiveTernary extends CtrPrimitive { // implements TagGuaranteedGAC

	protected final Variable x, y, z;
	protected Domain domx, domy, domz;

	public CtrPrimitiveTernary(Problem pb, Variable x, Variable y, Variable z) {
		super(pb, pb.api.vars(x, y, z));
		this.x = x;
		this.y = y;
		this.z = z;
		domx = x.dom;
		domy = y.dom;
		domz = z.dom;
	}

}
