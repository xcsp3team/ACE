/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problem;

import java.util.Map;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.IVar;
import org.xcsp.modeler.definitions.ICtr;

import constraints.Constraint;
import constraints.CtrIntension;
import constraints.extension.CtrExtension;
import utility.Kit;
import variables.Variable;

/**
 * XCSP instance compiler 3.0
 */
public final class Compiler3Abscon extends org.xcsp.modeler.Compiler {

	protected final Problem pb;
	protected final Subproblem subpb;

	public Compiler3Abscon(Subproblem subpb) {
		super(subpb.pb.api);
		this.pb = subpb.pb;
		this.subpb = subpb;
		ignoreAutomaticGroups = pb.rs.cp.settingXml.ignoreAutomaticGroups;
		saveImmediatelyStored = pb.rs.cp.settingXml.saveImmediatelyStored;
	}

	@Override
	protected Document buildDocument() {
		specificAbscon();
		return super.buildDocument();
	}

	@Override
	protected void putInMap(IVar x, Map<IVar, String> map) {
		map.put(x, ((Variable) x).dom.stringListOfValues());
	}

	// protected Function<? super IVar, ? extends Object> varClassifier() {
	// return x -> ((Variable) x).dom.typeIdentifier;
	// }
	// protected Function<? super IVar, ? extends Object> varClassifier() {
	// return x -> varToDom.get(x); // ((MVariable) x).dom;
	// }

	@Override
	protected Element variables() {
		if (!subpb.isFullProblem()) {
			throw new UnsupportedOperationException();
			// for each varAlone, if not present then remove from the map. for each VarArray, if not all variables are present, then remove
			// from the map and build VarAlone variables for those present and put them in the map of stuff. After that execute the code
			// below
		}
		return super.variables();
	}

	@Override
	protected void handleCtr(Element parent, ICtr ctr) {
		if (((Constraint) ctr).pb.optimizer != null && ((Constraint) ctr).pb.optimizer.ctr == ctr)
			return;
		super.handleCtr(parent, ctr);
	}

	@Override
	protected Element constraints() {
		if (!subpb.isFullProblem()) {
			throw new UnsupportedOperationException();
			// IntStream.range(0, ctrs.length).filter(i -> subpb.isPresentCtr(i)).forEach(i -> handleCtr(root, ctrs[i]));
		}
		return super.constraints();
	}

	private void specificAbscon() {
		Kit.control(subpb.isFullProblem(), () -> "currently, only full problems handled");
		if (pb.ctrEntities.ctrToCtrArray.size() == 0 && !ignoreAutomaticGroups) {
			CtrExtension[] ces = Stream.of(pb.constraints).filter(c -> c instanceof CtrExtension).map(c -> (CtrExtension) c).toArray(CtrExtension[]::new);
			if (ces.length > 1)
				pb.ctrEntities.newCtrArrayEntity(ces, false); // .note("Automatic set of extension constraints");
			CtrIntension[] cis = Stream.of(pb.constraints).filter(c -> c instanceof CtrIntension).map(c -> (CtrIntension) c).toArray(CtrIntension[]::new);
			if (cis.length > 1)
				pb.ctrEntities.newCtrArrayEntity(cis, false); // .note("Automatic set of intension constraints");
		}
	}

}
