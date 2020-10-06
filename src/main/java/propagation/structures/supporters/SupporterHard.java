/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package propagation.structures.supporters;

import constraints.CtrHard;
import variables.Variable;

public abstract class SupporterHard extends Supporter<CtrHard> {

	/**
	 * MUST be called when the constraint relation is modified
	 */
	public abstract void reset();

	public SupporterHard(CtrHard c) {
		super(c);
	}

	public abstract boolean findArcSupportFor(int x, int a);

	public boolean findArcSupportFor(Variable x, int a) {
		return findArcSupportFor(c.positionOf(x), a);
	}

}