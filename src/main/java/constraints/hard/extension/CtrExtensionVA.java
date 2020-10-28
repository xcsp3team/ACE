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
import constraints.hard.extension.structures.TableWithSubtables;
import constraints.hard.extension.structures.TableWithSubtablesExperimental1;
import constraints.hard.extension.structures.Tries;
import interfaces.TagPositive;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public class CtrExtensionVA extends CtrExtension implements TagPositive {

	@Override
	protected ExtensionStructureHard buildExtensionStructure() {
		if (pb.rs.cp.settingExtension.variant == 0)
			return new TableWithSubtables(this);
		if (pb.rs.cp.settingExtension.variant == 1 || pb.rs.cp.settingExtension.variant == 11)
			return new Tries(this, pb.rs.cp.settingExtension.variant == 11);
		return new TableWithSubtablesExperimental1(this);
	}

	public CtrExtensionVA(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	private final boolean seekSupportVA(int x, int a, int[] tuple, boolean another) {
		if (!another)
			tupleManager.firstValidTupleWith(x, a, tuple);
		else if (tupleManager.nextValidTupleCautiously() == -1)
			return false;
		while (true) {
			int[] t = extStructure.nextSupport(x, a, tuple);
			if (t == tuple)
				break;
			if (t == null)
				return false;
			Kit.copy(t, tuple);
			if (isValid(tuple))
				break;
			if (tupleManager.nextValidTupleCautiously() == -1)
				return false;
		}
		return true;
	}

	@Override
	public final boolean seekFirstSupportWith(int x, int a, int[] buffer) {
		buffer[x] = a;
		return seekSupportVA(x, a, buffer, false);
	}

}