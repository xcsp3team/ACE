/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package constraints.hard.extension;

import constraints.hard.CtrExtension;
import constraints.hard.extension.structures.ExtensionStructureHard;
import constraints.hard.extension.structures.Table;
import problem.Problem;
import utility.Reflector;
import variables.Variable;

/**
 * Involves iterating lists of valid tuples in order to find a support.
 */
public final class CtrExtensionV extends CtrExtension {

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		if (scp.length == 2 || scp.length == 3) {
			String className = scp.length == 2 ? pb.rs.cp.settingExtension.classForBinaryExtensionStructure : pb.rs.cp.settingExtension.classForTernaryExtensionStructure;
			return Reflector.buildObject(className, ExtensionStructureHard.class, this);
		} else
			return new Table(this); // MDD(this);
	}

	public CtrExtensionV(Problem pb, Variable[] scp) {
		super(pb, scp);
	}
}