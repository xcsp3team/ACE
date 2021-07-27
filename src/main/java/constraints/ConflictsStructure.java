/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;

import constraints.Constraint.RegisteringCtrs;
import constraints.extension.Extension.ExtensionGeneric;
import constraints.extension.structures.ExtensionStructure;
import constraints.intension.Intension;
import constraints.intension.Intension.SharedTreeEvaluator;
import interfaces.FilteringSpecific;
import problem.Problem;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class ConflictsStructure implements RegisteringCtrs {

	/*************************************************************************
	 * Static
	 *************************************************************************/

	static final BigInteger LIMIT_FOR_BARY = BigInteger.valueOf(1000000);

	static final BigInteger LIMIT_FOR_NARY = BigInteger.valueOf(10000);

	public static void buildFor(Problem problem) {
		if (!problem.head.control.mustBuildConflictStructures)
			return;
		for (ExtensionStructure extStructure : problem.head.structureSharing.mapOfExtensionStructures.values()) {
			Constraint c = extStructure.firstRegisteredCtr();
			if (c instanceof FilteringSpecific || c.scp.length == 1 || c.infiniteDomainVars.length > 0)
				continue;
			Kit.control(c instanceof ExtensionGeneric);
			if (Kit.memory() > 400000000L) // TODO hard coding
				return;
			ConflictsStructure conflictsStructure = new ConflictsStructure(c).initializeFrom(extStructure.originalTuples, extStructure.originalPositive);
			for (Constraint cc : extStructure.registeredCtrs) {
				cc.conflictsStructure = conflictsStructure;
				if (cc != c)
					conflictsStructure.register(cc);
			}
		}
		for (SharedTreeEvaluator treeEvaluator : problem.head.structureSharing.mapOfTreeEvaluators.values()) {
			Constraint c = treeEvaluator.firstRegisteredCtr();
			if (c instanceof FilteringSpecific || c.scp.length == 1 || c.infiniteDomainVars.length > 0)
				continue;
			Kit.control(c instanceof Intension);
			if (Kit.memory() > 400000000L) // TODO hard coding
				return;
			if (Domain.nValidTuples(c.doms, false).compareTo(c.scp.length == 2 ? LIMIT_FOR_BARY : LIMIT_FOR_NARY) > 0)
				continue;
			ConflictsStructure conflictsStructure = new ConflictsStructure(c).initialize();
			for (Constraint cc : treeEvaluator.registeredCtrs) {
				cc.conflictsStructure = conflictsStructure;
				if (cc != c)
					conflictsStructure.register(cc);
			}
		}
	}

	/*************************************************************************
	 * Methods
	 *************************************************************************/

	private List<Constraint> registeredCtrs = new ArrayList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	/**
	 * The first index of the array denotes the position (order) of each variable involved in the constraint. <br>
	 * The second index of the array denotes the different indexes of the values in the domain of the variable given by the first index. Each value of the array
	 * gives the number of conflicts for the corresponding pair composed of a variable and an index (of a value).
	 */
	public int[][] nConflicts; // [x][a]

	public int[] nMaxConflicts; // [x]

	public ConflictsStructure(Constraint c) {
		registeredCtrs.add(c);
		nMaxConflicts = new int[c.scp.length];
		nConflicts = Variable.litterals(c.scp).intArray();
	}

	public ConflictsStructure(ConflictsStructure conflictsStructure, Constraint c) {
		registeredCtrs.add(c);
		nMaxConflicts = conflictsStructure.nMaxConflicts.clone();
		nConflicts = Kit.cloneDeeply(conflictsStructure.nConflicts);
	}

	private void computeNbMaxConflicts() {
		Domain[] doms = firstRegisteredCtr().doms;
		for (int i = 0; i < nMaxConflicts.length; i++) {
			int max = Integer.MIN_VALUE;
			Domain dom = doms[i];
			for (int a = dom.first(); a != -1; a = dom.next(a))
				max = Math.max(max, nConflicts[i][a]);
			nMaxConflicts[i] = max;
		}
	}

	private ConflictsStructure initializeFrom(int[][] tuples, boolean positive) {
		assert registeredCtrs.size() == 1;
		Domain[] doms = firstRegisteredCtr().doms;
		extern: for (int[] tuple : tuples) {
			assert IntStream.of(tuple).noneMatch(v -> v == Constants.STAR);
			for (int i = 0; i < tuple.length; i++)
				if (!doms[i].containsValue(tuple[i]))
					continue extern;
			for (int i = 0; i < tuple.length; i++)
				nConflicts[i][doms[i].toIdx(tuple[i])]++;
		}
		if (positive) {
			int nValidTuples = Domain.nValidTuples(doms, false).intValueExact();
			for (int i = 0; i < nConflicts.length; i++) {
				int nTuples = nValidTuples / doms[i].size();
				for (int j = 0; j < nConflicts[i].length; j++)
					nConflicts[i][j] = nTuples - nConflicts[i][j];
			}
		}
		// because the nb of supports was computed and stored in nbConflicts
		computeNbMaxConflicts();
		assert controlStructures();
		return this;
	}

	private ConflictsStructure initialize() {
		assert registeredCtrs.size() == 1;
		Constraint c = firstRegisteredCtr();
		c.tupleManager.firstValidTuple();
		c.tupleManager.overValidTuples(t -> {
			if (!c.checkIndexes(t))
				for (int i = 0; i < t.length; i++)
					nConflicts[i][t[i]]++;
		});
		computeNbMaxConflicts();
		assert controlStructures();
		return this;
	}

	private boolean controlStructures() {
		Constraint c = firstRegisteredCtr();
		if (Domain.nValidTuples(c.doms, false).compareTo(LIMIT_FOR_NARY) > 0) {
			Kit.log.warning("Too large Cartesian Space for checking ");
			return true;
		}
		for (int i = 0; i < nConflicts.length; i++) {
			Variable x = c.scp[i];
			int max = Integer.MIN_VALUE;
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				Kit.control(nConflicts[i][a] == c.nConflictsFor(i, a), "pb with " + c + " " + x);
				max = Math.max(max, nConflicts[i][a]);
			}
			Kit.control(max == nMaxConflicts[i], "pb with " + c + " " + x);
		}
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("In ").append(firstRegisteredCtr()).append(" (nCtrs=").append(registeredCtrs.size()).append(")");
		for (int i = 0; i < nConflicts.length; i++)
			sb.append("\n  ").append(i).append(" : nMaxConflicts=").append(nMaxConflicts[i]).append("  nConflicts=(").append(Kit.join(nConflicts[i]));
		return sb.toString();
	}
}