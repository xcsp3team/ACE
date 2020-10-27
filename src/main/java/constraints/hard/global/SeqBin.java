package constraints.hard.global;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.TreeEvaluator;
import org.xcsp.common.predicates.XNodeParent;

import constraints.hard.CtrGlobal;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.VariableInteger;

public class SeqBin extends CtrGlobal implements TagGACGuaranteed, TagFilteringCompleteAtEachCall { // TODO : control complet filtering at
																									// each call

	protected final Variable k;
	protected final Variable[] vector;
	protected final TreeEvaluator[] c;
	protected final TreeEvaluator[] b;

	/**
	 * Useful to make a bijection between domain values and array indices in the costs structures.
	 */
	protected final int smallestDomVal;

	/**
	 * Built once and for all to avoid building an int[] at each evaluation.
	 */
	private final int[] evaluatedValues = new int[2];

	/**
	 * Built once and for all, list of indexes to prune from a domain.
	 */
	protected final List<Integer> idxsToPrune = new ArrayList<>();

	/**
	 * For each variable, for each value, stores a cost set represented as a boolean array. Forward and backward are the result of a forward and a
	 * backward path searches in a n-partite graph where n=vector.length. For more details, see PathDP algorithm described in article The SEQBIN
	 * Constraint Revisited from George Katsirelos et al.
	 */
	protected final CostSet[][] totalCosts;
	protected final CostSet[][] forwardCosts;
	protected final CostSet[][] backwardCosts;
	protected final CostSet costSetOfK;

	/**
	 * This constraint ensures that the number of violations of a given binary constraint c on each pair of consecutive variables in vector is equal
	 * to k-1. It can also enforce another constraint b on those variable pairs.
	 * 
	 * @param pb
	 *            : The problem the constraint is attached to.
	 * @param k
	 *            : Number of violations of the c constraints.
	 * @param vector
	 *            : A vector of variables.
	 * @param cOp
	 *            : Binary relational operator defining the c constraints between each two consecutive variables in vector.
	 */
	public SeqBin(Problem pb, VariableInteger k, VariableInteger[] vector, TypeConditionOperatorRel cOp, TypeConditionOperatorRel bOp) {
		super(pb, pb.api.vars(k, vector));
		Kit.control(Variable.haveAllSameDomainType(vector));
		k.dom.removeValuesLT(1);
		k.dom.removeValuesGT(vector.length);
		this.k = k;
		this.vector = vector;
		c = new TreeEvaluator[vector.length - 1];
		TypeExpr ce = Types.valueOf(TypeExpr.class, cOp.toString());
		int smallestDomVal = vector[vector.length - 1].dom.firstValue();
		int greatestDomVal = vector[vector.length - 1].dom.firstValue();
		for (int varPos = 0; varPos < vector.length - 1; varPos++) {
			// String[] pred = pb.build(ce, vector[varPos], vector[varPos + 1]).canonicalForm(new ArrayList<>(), pb.vars(vector[varPos],
			// vector[varPos + 1]))
			// .toArray(new String[0]);
			XNodeParent<IVar> tree = XNodeParent.build(ce, vector[varPos], vector[varPos + 1]);
			c[varPos] = new TreeEvaluator(tree); // pb.vars(vector[varPos], vector[varPos + 1]), pb.build(ce,
													// vector[varPos], vector[varPos + 1]));
			if (smallestDomVal > vector[varPos].dom.firstValue())
				smallestDomVal = vector[varPos].dom.firstValue();
			if (greatestDomVal < vector[varPos].dom.lastValue())
				greatestDomVal = vector[varPos].dom.lastValue();
		}
		if (bOp == null)
			b = null;
		else {
			b = new TreeEvaluator[vector.length - 1];
			TypeExpr be = Types.valueOf(TypeExpr.class, bOp.toString());
			for (int i = 0; i < b.length; i++) {
				XNodeParent<IVar> tree = XNodeParent.build(be, vector[i], vector[i + 1]);
				// String[] pred = pb.build(be, vector[i], vector[i + 1]).canonicalForm(new ArrayList<>(), pb.vars(vector[i], vector[i +
				// 1]))
				// .toArray(new String[0]);
				b[i] = new TreeEvaluator(tree);
				// b[i] = new EvaluationManager(be.postfixExpressionFor(vector[i], vector[i + 1]).split(Kit.REG_WS));
			}
		}
		this.smallestDomVal = smallestDomVal;
		totalCosts = new CostSet[vector.length][];
		forwardCosts = new CostSet[vector.length][];
		backwardCosts = new CostSet[vector.length][];
		for (int varPos = 0; varPos < vector.length; varPos++) {
			totalCosts[varPos] = new CostSet[greatestDomVal - smallestDomVal + 1];
			forwardCosts[varPos] = new CostSet[greatestDomVal - smallestDomVal + 1];
			backwardCosts[varPos] = new CostSet[greatestDomVal - smallestDomVal + 1];
			for (int valPos = 0; valPos < totalCosts[varPos].length; valPos++) {
				totalCosts[varPos][valPos] = new CostSet(vector.length);
				forwardCosts[varPos][valPos] = new CostSet(vector.length);
				backwardCosts[varPos][valPos] = new CostSet(vector.length);
			}
		}
		costSetOfK = new CostSet(vector.length);
	}

	@Override
	public int[] defineSymmetryMatching() {
		return Kit.range(1, scp.length);
	}

	@Override
	public boolean checkValues(int[] vals) {
		if (b != null)
			for (int evalPos = 0; evalPos < b.length; evalPos++)
				if (evaluate(b[evalPos], vals[evalPos + 1], vals[evalPos + 2]) != 1)
					return false;
		return checkNumberOfCViolations(vals);
	}

	// @Override
	// public DefXCSP defXCSP() {
	// // TODO Auto-generated method stub
	// return null;
	// }

	@Override
	public boolean runPropagator(Variable evt) {
		if (!propagateBConstraints())
			return false;
		pathDP();
		if (!pruneK())
			return false;
		return pruneVector();
	}

	/**
	 * Checks the number of violations among all the c binary constraints.
	 * 
	 * @param vals
	 *            : An instantiation of all the variables of the constraint.
	 * @return true iff the number of violations in the c constraints is equal to vals[0] - 1, and thus matches the instantiation of the k variable.
	 */
	protected boolean checkNumberOfCViolations(int[] vals) {
		int cnt = 1;
		for (int evalPos = 0; evalPos < c.length; evalPos++)
			cnt += evaluate(c[evalPos], vals[evalPos + 1], vals[evalPos + 2]);
		return cnt == vals[0];
	}

	protected long evaluate(TreeEvaluator eval, int operand1, int operand2) {
		evaluatedValues[0] = operand1;
		evaluatedValues[1] = operand2;
		return eval.evaluate(evaluatedValues);
	}

	protected boolean propagateBConstraints() {
		if (b != null) {
			for (int varPos = 1; varPos < vector.length; varPos++) {
				idxsToPrune.clear();
				for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx)) {
					boolean support = false;
					// TODO (optim) : version where a support is stored for each couple (var,idx).
					for (int idxPrev = vector[varPos - 1].dom.first(); idxPrev != -1; idxPrev = vector[varPos - 1].dom.next(idxPrev))
						if (evaluate(b[varPos - 1], vector[varPos - 1].dom.toVal(idxPrev), vector[varPos].dom.toVal(idx)) == 1) {
							support = true;
							break;
						}
					if (!support)
						idxsToPrune.add(idx);
				}
				for (Integer idx : idxsToPrune)
					if (!vector[varPos].dom.remove(idx))
						return false;
			}
			for (int varPos = vector.length - 2; varPos >= 0; varPos--) {
				idxsToPrune.clear();
				for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx)) {
					boolean support = false;
					// TODO (optim) : version where a support is stored for each couple (var,idx).
					for (int idxNext = vector[varPos + 1].dom.first(); idxNext != -1; idxNext = vector[varPos + 1].dom.next(idxNext))
						if (evaluate(b[varPos], vector[varPos].dom.toVal(idx), vector[varPos + 1].dom.toVal(idxNext)) == 1) {
							support = true;
							break;
						}
					if (!support)
						idxsToPrune.add(idx);
				}
				for (Integer idx : idxsToPrune)
					if (!vector[varPos].dom.remove(idx))
						return false;
			}
		}
		return true;
	}

	/**
	 * Fills the forwardCosts, backwardCosts, totalCosts and costSetOfK structures using the PathDP algorithm described in The SEQBIN Constraint
	 * Revisited from George Katsirelos et al.
	 */
	protected void pathDP() {

		// Initialize structures

		for (int valPos = 0; valPos < totalCosts[0].length; valPos++) {
			backwardCosts[0][valPos].add(0);
			forwardCosts[forwardCosts.length - 1][valPos].add(0);
		}

		// Compute forwardCosts

		for (int varPos = forwardCosts.length - 2; varPos >= 0; varPos--) {
			for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx)) {
				int val = vector[varPos].dom.toVal(idx);
				forwardCosts[varPos][val - smallestDomVal].clear();
				for (int idxNext = vector[varPos + 1].dom.first(); idxNext != -1; idxNext = vector[varPos + 1].dom.next(idxNext)) {
					int valNext = vector[varPos + 1].dom.toVal(idxNext);
					if (b == null || evaluate(b[varPos], val, valNext) == 1)
						forwardCosts[varPos][val - smallestDomVal].updateFromArc(forwardCosts[varPos + 1][valNext - smallestDomVal],
								(int) evaluate(c[varPos], val, valNext));
				}
			}
		}

		// Compute backwardCosts

		for (int varPos = 1; varPos < backwardCosts.length; varPos++) {
			for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx)) {
				int val = vector[varPos].dom.toVal(idx);
				backwardCosts[varPos][val - smallestDomVal].clear();
				for (int idxPrev = vector[varPos - 1].dom.first(); idxPrev != -1; idxPrev = vector[varPos - 1].dom.next(idxPrev)) {
					int valPrev = vector[varPos - 1].dom.toVal(idxPrev);
					if (b == null || evaluate(b[varPos - 1], valPrev, val) == 1)
						backwardCosts[varPos][val - smallestDomVal].updateFromArc(backwardCosts[varPos - 1][valPrev - smallestDomVal],
								(int) evaluate(c[varPos - 1], valPrev, val));
				}
			}
		}

		// Compute totalCosts

		for (int varPos = 0; varPos < totalCosts.length; varPos++)
			for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx)) {
				int valPos = vector[varPos].dom.toVal(idx) - smallestDomVal;
				totalCosts[varPos][valPos].unionSum(forwardCosts[varPos][valPos], backwardCosts[varPos][valPos]);
			}

		// Compute costSetOfK

		costSetOfK.clear();
		for (int idx = vector[0].dom.first(); idx != -1; idx = vector[0].dom.next(idx))
			costSetOfK.addAll(totalCosts[0][vector[0].dom.toVal(idx) - smallestDomVal]);
		assert areCostStructuresCoherent();
	}

	/**
	 * Prunes the domain of variable k according to costSetOfK.
	 * 
	 * @return false in case of domain wipeout, true otherwise.
	 */
	protected boolean pruneK() {
		idxsToPrune.clear();
		for (int idx = k.dom.first(); idx != -1; idx = k.dom.next(idx))
			if (!costSetOfK.contains(k.dom.toVal(idx) - 1))
				idxsToPrune.add(idx);
		for (Integer idx : idxsToPrune)
			if (!k.dom.remove(idx))
				return false;
		return true;
	}

	/**
	 * Prunes the domains of variables in vector according to totalCosts and the domain of k.
	 * 
	 * @return false in case of domain wipeout, true otherwise.
	 */
	protected boolean pruneVector() {
		for (int i = 0; i < vector.length; i++) {
			idxsToPrune.clear();
			for (int idx = vector[i].dom.first(); idx != -1; idx = vector[i].dom.next(idx)) {
				int valPos = vector[i].dom.toVal(idx) - smallestDomVal;
				boolean support = false;
				// TODO (optim) : version where a support is stored for each couple (var,idx).
				for (int idxK = k.dom.first(); idxK != -1; idxK = k.dom.next(idxK)) {
					int valK = k.dom.toVal(idxK);
					if (totalCosts[i][valPos].contains(valK - 1)) {
						support = true;
						break;
					}
				}
				if (!support)
					idxsToPrune.add(idx);
			}
			for (Integer idx : idxsToPrune)
				if (!vector[i].dom.remove(idx))
					return false;
		}

		return true;
	}

	/**
	 * Only for debug, tests the consistency of totalCosts and costSetOfK.
	 * 
	 * @return true iff the totalCosts sets union for each variable are all equal.
	 */
	private boolean areCostStructuresCoherent() {
		CostSet currentCostSet = new CostSet(vector.length);
		for (int varPos = 0; varPos < totalCosts.length; varPos++) {
			List<CostSet> costSets = new ArrayList<>();
			for (int idx = vector[varPos].dom.first(); idx != -1; idx = vector[varPos].dom.next(idx))
				costSets.add(totalCosts[varPos][vector[varPos].dom.toVal(idx) - smallestDomVal]);
			currentCostSet.union(costSets.toArray(new CostSet[costSets.size()]));
			if (!currentCostSet.equals(costSetOfK))
				return false;
		}
		return true;
	}

	/**
	 * Structure used to represent a set of values (costs). A value v belongs to the set iff costs[v] == true.
	 */
	protected class CostSet {

		private boolean[] costs;
		private int size;

		protected CostSet(int size) {
			Kit.control(size > 0);
			costs = new boolean[size];
			this.size = size;
		}

		protected void add(int cost) {
			Kit.control(cost >= 0 && cost < size);
			costs[cost] = true;
		}

		protected void addAll(CostSet other) {
			Kit.control(size == other.size);
			for (int i = 0; i < size; i++)
				if (other.contains(i))
					add(i);
		}

		protected void remove(int cost) {
			Kit.control(cost >= 0 && cost < size);
			costs[cost] = false;
		}

		protected boolean contains(int cost) {
			Kit.control(cost >= 0 && cost < size);
			return costs[cost];
		}

		protected void clear() {
			for (int i = 0; i < size; i++)
				remove(i);
		}

		protected boolean isEmpty() {
			for (int i = 0; i < size; i++)
				if (contains(i))
					return false;
			return true;
		}

		protected boolean equals(CostSet other) {
			if (this == other)
				return true;
			if (size != other.size)
				return false;
			for (int i = 0; i < size; i++)
				if (contains(i) != other.contains(i))
					return false;
			return true;
		}

		/**
		 * <b>this</b> becomes a CostSet containing all the possible sums i+j such that i is in set1 and j is in set2.
		 */
		protected void unionSum(CostSet set1, CostSet set2) {
			Kit.control(size == set1.size && set1.size == set2.size);
			clear();
			if (set1.isEmpty())
				addAll(set2);
			else if (set2.isEmpty())
				addAll(set1);
			else
				for (int i = 0; i < size; i++)
					for (int j = 0; j < size; j++)
						if (set1.contains(i) && set2.contains(j))
							add(i + j);
		}

		protected void updateFromArc(CostSet other, int cost) {
			for (int i = 0; i < other.size; i++)
				if (other.contains(i))
					add(i + cost);
		}

		protected void union(CostSet... sets) {
			Kit.control(sets.length >= 1 && size == sets[0].size);
			for (int i = 0; i < sets.length - 1; i++)
				Kit.control(sets[i].size == sets[i + 1].size);
			clear();
			for (int j = 0; j < size; j++)
				for (int i = 0; i < sets.length; i++)
					if (sets[i].contains(j)) {
						add(j);
						break;
					}
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("{");
			boolean first = true;
			for (int i = 0; i < size; i++)
				if (contains(i)) {
					sb.append(first ? i : ("," + i));
					first = false;
				}
			sb.append("}");
			return sb.toString();
		}
	}
}
