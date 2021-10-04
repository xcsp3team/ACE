/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints;

import static utility.Kit.control;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.Constants;

import constraints.ConstraintExtension.ExtensionGeneric;
import constraints.ConstraintIntension.IntensionStructure;
import constraints.extension.structures.ExtensionStructure;
import heuristics.HeuristicValuesDynamic.Conflicts;
import interfaces.ConstraintRegister;
import interfaces.SpecificPropagator;
import problem.Problem;
import propagation.Reviser;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This class allows us to record some information about the number of conflicts (disallowed tuples) for pairs (x,a) in
 * the context of a constraint. This can be useful for some forms of reasoning (like, for example, avoiding a useless
 * filtering operation). Such structures are only relevant for some intension and extension constraints.
 * 
 * @author Christophe Lecoutre
 */
public final class ConflictsStructure implements ConstraintRegister {

	/*************************************************************************
	 * Implementing interfaces
	 *************************************************************************/

	private List<Constraint> registeredCtrs = new ArrayList<>();

	@Override
	public List<Constraint> registeredCtrs() {
		return registeredCtrs;
	}

	/*************************************************************************
	 * Static members
	 *************************************************************************/

	/**
	 * The limit in term of number of tuples, for binary constraints, to decide if the conflicts structure must be built
	 */
	private static final BigInteger BARY_VALID_LIMIT = BigInteger.valueOf(1000000);

	/**
	 * The limit in term of number of tuples, for non binary constraints, to decide if the conflicts structure must be
	 * built
	 */
	private static final BigInteger NARY_VALID_LIMIT = BigInteger.valueOf(10000);

	/**
	 * The memory limit to deciding if the conflicts structure must be built
	 */
	private static final long MEMORY_LIMIT = 400000000L;

	/**
	 * Attempts to build some structures recording the number of conflicts (disallowed tuples) for each pair (x,a). This
	 * can be useful for some forms of reasoning (like, for example, avoiding a useless filtering operation). Such
	 * structures are only relevant for some intension and extension constraints.
	 * 
	 * @param problem
	 *            a problem
	 */
	public static void buildFor(Problem problem) {
		if (problem.head.control.propagation.reviser.equals(Reviser.class.getSimpleName())
				&& problem.head.control.valh.clazz.equals(Conflicts.class.getSimpleName()))
			return;
		for (IntensionStructure structure : problem.head.structureSharing.mapForIntension.values()) {
			ConstraintIntension c1 = (ConstraintIntension) structure.firstRegisteredCtr();
			if (c1.scp.length == 1 || c1.infiniteDomainVars.length > 0)
				continue;
			if (Kit.memory() > MEMORY_LIMIT)
				return;
			if (Domain.nValidTuples(c1.doms, false).compareTo(c1.scp.length == 2 ? BARY_VALID_LIMIT : NARY_VALID_LIMIT) > 0)
				continue;
			ConflictsStructure conflictsStructure = new ConflictsStructure(c1);
			for (Constraint c : structure.registeredCtrs()) {
				c.conflictsStructure = conflictsStructure;
				if (c != c1)
					conflictsStructure.register(c);
			}
		}
		for (ExtensionStructure structure : problem.head.structureSharing.mapForExtension.values()) {
			ConstraintExtension c1 = (ConstraintExtension) structure.firstRegisteredCtr();
			if (c1 instanceof SpecificPropagator || c1.scp.length == 1 || c1.infiniteDomainVars.length > 0)
				continue;
			control(c1 instanceof ExtensionGeneric);
			if (Kit.memory() > MEMORY_LIMIT)
				return;
			ConflictsStructure conflictsStructure = new ConflictsStructure(c1);
			for (Constraint c : structure.registeredCtrs()) {
				c.conflictsStructure = conflictsStructure;
				if (c != c1)
					conflictsStructure.register(c);
			}
		}
	}

	/*************************************************************************
	 * Class members
	 *************************************************************************/

	/**
	 * nConflicts[x][a] is the number of conflicts for (x,a) where x is the position of a variable in the constraint
	 * scope and a an index of value.
	 */
	public int[][] nConflicts;

	/**
	 * nMaxConflicts[x] is the maximal number of conflicts when considering all pairs (x,a) where x is the position of a
	 * variable in the constraint scope and a an index of value
	 */
	public int[] nMaxConflicts;

	private void computeMaxConflicts(Domain[] doms) {
		for (int i = 0; i < nMaxConflicts.length; i++) {
			int max = Integer.MIN_VALUE;
			for (int a = doms[i].first(); a != -1; a = doms[i].next(a))
				max = Math.max(max, nConflicts[i][a]);
			nMaxConflicts[i] = max;
		}
		assert controlStructures();
	}

	/**
	 * Builds a conflicts structure for the specified constraint.
	 * 
	 * @param c
	 *            a constraint
	 */
	private ConflictsStructure(Constraint c) {
		this.nConflicts = Variable.litterals(c.scp).intArray();
		this.nMaxConflicts = new int[c.scp.length];
		registeredCtrs.add(c);
	}

	/**
	 * Builds a conflicts structure for the specified intension constraint.
	 * 
	 * @param c
	 *            an intension constraint
	 */
	public ConflictsStructure(ConstraintIntension c) {
		this((Constraint) c);
		c.tupleIterator.firstValidTuple();
		c.tupleIterator.consumeValidTuples(t -> {
			if (!c.checkIndexes(t))
				for (int i = 0; i < t.length; i++)
					nConflicts[i][t[i]]++;
		});
		computeMaxConflicts(c.doms);
	}

	/**
	 * Builds a conflicts structure for the specified extension constraint.
	 * 
	 * @param c
	 *            an extension constraint
	 */
	public ConflictsStructure(ConstraintExtension c) {
		this((Constraint) c);
		extern: for (int[] tuple : c.extStructure.originalTuples) {
			assert IntStream.of(tuple).noneMatch(v -> v == Constants.STAR);
			for (int i = 0; i < tuple.length; i++)
				if (!c.doms[i].containsValue(tuple[i]))
					continue extern;
			for (int i = 0; i < tuple.length; i++)
				nConflicts[i][c.doms[i].toIdx(tuple[i])]++;
		}
		if (c.extStructure.originalPositive) {
			int nValidTuples = Domain.nValidTuples(c.doms, false).intValueExact();
			for (int i = 0; i < nConflicts.length; i++) {
				int nTuples = nValidTuples / c.doms[i].size();
				for (int j = 0; j < nConflicts[i].length; j++)
					nConflicts[i][j] = nTuples - nConflicts[i][j];
			}
		}
		computeMaxConflicts(c.doms);
	}

	/**
	 * Builds a conflicts structure for the specified constraint by cloning the specified conflicts structure.
	 * 
	 * @param c
	 *            a constraint
	 * @param conflictsStructure
	 *            a conflicts structure to be cloned
	 */
	public ConflictsStructure(Constraint c, ConflictsStructure conflictsStructure) {
		this.nConflicts = Kit.cloneDeeply(conflictsStructure.nConflicts);
		this.nMaxConflicts = conflictsStructure.nMaxConflicts.clone();
		registeredCtrs.add(c);
	}

	private boolean controlStructures() {
		Constraint c = firstRegisteredCtr();
		if (Domain.nValidTuples(c.doms, false).compareTo(NARY_VALID_LIMIT) > 0) {
			Kit.log.warning("Too large Cartesian Space for checking ");
			return true;
		}
		for (int i = 0; i < nConflicts.length; i++) {
			Variable x = c.scp[i];
			int max = Integer.MIN_VALUE;
			for (int a = x.dom.first(); a != -1; a = x.dom.next(a)) {
				assert nConflicts[i][a] == c.nConflictsFor(i, a) : "pb with " + c + " " + x;
				max = Math.max(max, nConflicts[i][a]);
			}
			assert max == nMaxConflicts[i] : "pb with " + c + " " + x;
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