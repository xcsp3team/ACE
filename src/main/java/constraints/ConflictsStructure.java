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
import java.util.LinkedList;
import java.util.List;
import java.util.stream.IntStream;

import constraints.extension.ExtensionCT;
import constraints.extension.ExtensionCT.ExtensionCT2;
import constraints.extension.ExtensionSTR2;
import dashboard.ControlPanel;
import interfaces.RegisteringCtrs;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public final class ConflictsStructure implements RegisteringCtrs {

	/*************************************************************************
	 * Static
	 *************************************************************************/

	public static final int LIMIT_FOR_NARY = 10000;

	public static final int LIMIT_FOR_BARY = 1000000;

	private static boolean canBuildConflictsStructureFor(Constraint c, int limit) {
		if (c instanceof ExtensionSTR2 || c instanceof ExtensionCT || c instanceof ExtensionCT2 || c.infiniteDomainVars.length > 0)
			return false;
		ControlPanel cfg = c.pb.head.control;
		if (!cfg.mustBuildConflictStructures || c.scp.length == 1 || Kit.memory() > 400000000L)
			return false;
		return Variable.nValidTuples(c.scp, false).compareTo(BigInteger.valueOf(limit)) <= 0;
	}

	public static ConflictsStructure build(Constraint ctr, int[][] tuples, boolean positive) {
		return canBuildConflictsStructureFor(ctr, Integer.MAX_VALUE) ? new ConflictsStructure(ctr).initializeFrom(tuples, positive) : null;
	}

	public static ConflictsStructure build(Constraint ctr) {
		return canBuildConflictsStructureFor(ctr, ctr.scp.length == 2 ? LIMIT_FOR_BARY : LIMIT_FOR_NARY) ? new ConflictsStructure(ctr).initialize() : null;
	}

	/*************************************************************************
	 * Methods
	 *************************************************************************/

	private List<Constraint> registeredCtrs = new LinkedList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	/**
	 * The first index of the array denotes the position (order) of each variable involved in the constraint. <br>
	 * The second index of the array denotes the different indexes of the values in the domain of the variable given by the first index. Each value of the array
	 * gives the number of conflicts for the corresponding pair composed of a variable and an index (of a value).
	 */
	private int[][] nConflicts; // [vap][idx]

	private int[] nbMaxConflicts; // [vap]

	public int[][] nConflicts() {
		return nConflicts;
	}

	public int[] nMaxConflicts() {
		return nbMaxConflicts;
	}

	public ConflictsStructure(Constraint ctr) {
		registeredCtrs.add(ctr);
		nbMaxConflicts = new int[ctr.scp.length];
		nConflicts = Variable.litterals(ctr.scp).intArray();
	}

	public ConflictsStructure(ConflictsStructure conflictsStructure, Constraint ctr) {
		registeredCtrs.add(ctr);
		nbMaxConflicts = conflictsStructure.nbMaxConflicts.clone();
		nConflicts = Kit.cloneDeeply(conflictsStructure.nConflicts);
	}

	public final void computeNbMaxConflicts() {
		assert registeredCtrs.size() == 1;
		Constraint ctr = firstRegisteredCtr();
		for (int i = 0; i < nbMaxConflicts.length; i++) {
			int max = Integer.MIN_VALUE;
			Domain dom = ctr.scp[i].dom;
			for (int idx = dom.first(); idx != -1; idx = dom.next(idx))
				max = Math.max(max, nConflicts[i][idx]);
			nbMaxConflicts[i] = max;
		}
	}

	private ConflictsStructure initializeFrom(int[][] tuples, boolean positive) {
		Constraint c = firstRegisteredCtr();
		assert registeredCtrs.size() == 1 && !c.usePredefinedMaxNumberOfConflicts();
		Variable[] scp = firstRegisteredCtr().scp;
		int nbValidTuples = Variable.nValidTuples(scp, false).intValueExact();
		int[] t = new int[scp.length];
		for (int[] tuple : tuples) {
			if (Variable.isValidTuple(scp, c.toIdxs(tuple, t), true))
				for (int i = 0; i < tuple.length; i++) {
					// Kit.prn(scope[i].domain.toIndex(tuple[i]));
					nConflicts[i][scp[i].dom.toIdx(tuple[i])]++;

				}
		}
		if (positive)
			for (int i = 0; i < nConflicts.length; i++)
				for (int j = 0; j < nConflicts[i].length; j++)
					nConflicts[i][j] = (nbValidTuples / scp[i].dom.size()) - nConflicts[i][j];
		// because the nb of supports was computed and stored in nbConflicts
		computeNbMaxConflicts();
		assert controlStructures();
		return this;
	}

	private ConflictsStructure initialize() {
		assert registeredCtrs.size() == 1;
		Constraint c = firstRegisteredCtr();
		if (c.usePredefinedMaxNumberOfConflicts()) {
			for (int i = 0; i < nConflicts.length; i++) {
				Variable x = c.scp[i];
				for (int j = 0; j < nConflicts[i].length; j++)
					nConflicts[i][j] = c.giveUpperBoundOfMaxNumberOfConflictsFor(x, j);
			}
		} else {
			c.tupleManager.firstValidTuple();
			c.tupleManager.overValidTuples(t -> {
				if (!c.checkIndexes(t))
					for (int i = 0; i < t.length; i++)
						nConflicts[i][t[i]]++;
			});
		}
		computeNbMaxConflicts();
		assert controlStructures();
		// Kit.prn(this);
		return this;
	}

	private Variable getReducedDomainVariable(Variable[] scope, int[] domainsFrontier) {
		Variable reducedDomainVariable = null;
		for (Variable var : scope)
			if (var.dom.lastRemoved() != domainsFrontier[var.num])
				if (reducedDomainVariable == null)
					reducedDomainVariable = var;
				else
					return Variable.TAG;
		return reducedDomainVariable;
	}

	public void updateCounters(int[] domainsFrontier) {
		assert registeredCtrs.size() == 1;
		Constraint constraint = firstRegisteredCtr();
		if (constraint.usePredefinedMaxNumberOfConflicts())
			return;
		Variable reducedDomainVariable = getReducedDomainVariable(constraint.scp, domainsFrontier);
		if (reducedDomainVariable == null)
			return;
		else if (reducedDomainVariable == Variable.TAG) {
			// for (int i = 0; i < nbConflicts.length; i++) Arrays.fill(nbConflicts[i], 0);
			// calling initialize ??? while controlling the effort ?
			return;
		}

		long nb = Variable.nValidTuplesBoundedAtMaxValueFor(constraint.scp, constraint.positionOf(reducedDomainVariable));
		if (nb < (constraint.scp.length == 2 ? LIMIT_FOR_BARY : LIMIT_FOR_NARY))
			manageRemovedValues(reducedDomainVariable, domainsFrontier[reducedDomainVariable.num]);
	}

	/**
	 * It is assumed that only the domain of the specified variable has been reduced (when considering the scope of the exploiting constraint).
	 */
	public void manageRemovedValues(Variable x, int sentinel) {
		Constraint c = firstRegisteredCtr();
		assert registeredCtrs.size() == 1 && !c.usePredefinedMaxNumberOfConflicts();
		int p = c.positionOf(x);
		TupleManager tupleManager = c.tupleManager;
		Domain dom = x.dom;
		for (int a = dom.lastRemoved(); a != sentinel; a = dom.prevRemoved(a)) {
			int nbUpdatesToBeDone = nConflicts[p][a];
			if (nbUpdatesToBeDone == 0)
				break;
			int[] tuple = tupleManager.firstValidTupleWith(p, a);
			while (true) {
				if (!c.checkIndexes(tuple)) {
					for (int i = 0; i < tuple.length; i++)
						if (i != p)
							nConflicts[i][tuple[i]]--;
					if (--nbUpdatesToBeDone == 0)
						break;
				}
				int pos = tupleManager.nextValidTuple();
				Kit.control(pos != -1, () -> "Should not be reached ");
			}
		}
		computeNbMaxConflicts();
		assert controlStructures();
	}

	/**
	 * We assume that the given array corresponds to an allowed tuple of indexes (and not to a tuple of values) that has just been removed.
	 */
	public final void manageRemovedTuple(int... idxs) {
		assert registeredCtrs.size() == 1 && !firstRegisteredCtr().usePredefinedMaxNumberOfConflicts();
		for (int i = 0; i < idxs.length; i++)
			if (++nConflicts[i][idxs[i]] > nbMaxConflicts[i])
				nbMaxConflicts[i]++;
	}

	public boolean possiblyRemoveValuesFor(Constraint ctr) {
		assert ctr.pb.solver.depth() == 0 && registeredCtrs.contains(ctr);
		long nbValidTuples = Variable.nValidTuplesBoundedAtMaxValueFor(ctr.scp);
		for (int i = 0; i < ctr.scp.length; i++) {
			int[] nbConflicts = nConflicts()[i];
			Domain dom = ctr.scp[i].dom;
			long nbValidTuplesOfValues = nbValidTuples / dom.size();
			for (int idx = dom.first(); idx != -1; idx = dom.next(idx))
				if (nbConflicts[idx] == nbValidTuplesOfValues)
					dom.removeElementary(idx);
			if (dom.size() == 0)
				return false;
		}
		return true;
	}

	public boolean controlStructures() {
		Constraint c = firstRegisteredCtr();
		if (c.usePredefinedMaxNumberOfConflicts())
			return true;
		if (Variable.nValidTuples(c.scp, false).compareTo(BigInteger.valueOf(LIMIT_FOR_NARY)) > 0) {
			Kit.log.warning("Too large Cartesian Space for checking ");
			return true;
		}
		IntStream.range(0, nConflicts.length).forEach(i -> {
			int max = Integer.MIN_VALUE;
			Domain dom = c.scp[i].dom;
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				Kit.control(nConflicts[i][a] == c.nConflictsFor(i, a), () -> "pb with " + c + " " + c.scp[i]);
				max = Math.max(max, nConflicts[i][a]);
			}
			Kit.control(max == nbMaxConflicts[i], () -> "pb with " + c + " " + c.scp[i]);
		});
		return true;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder().append("In ").append(firstRegisteredCtr()).append(" (nbExploitingConstraints=").append(registeredCtrs.size())
				.append(")\n");
		for (int i = 0; i < nConflicts.length; i++)
			sb.append("  ").append(i).append(" : nbmaxConflicts=").append(nbMaxConflicts[i]).append("  nbConflicts=(").append(Kit.join(nConflicts[i]))
					.append(")\n");
		return sb.toString();
	}
}