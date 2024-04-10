/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.extension.structures;

import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;
import static org.xcsp.common.Types.TypeConditionOperatorSet.IN;
import static org.xcsp.common.Types.TypeConditionOperatorSet.NOTIN;
import static org.xcsp.common.Utilities.safeInt;
import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.common.structures.AbstractTuple;
import org.xcsp.common.structures.AbstractTuple.OrdinaryTuple;

import constraints.ConstraintExtension;
import constraints.extension.CHybrid;
import sets.SetDense;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.DomainFinite.DomainSymbols;
import variables.Variable;

/**
 * This is the class for representing hybrid (smart) tables.
 * 
 * @author Christophe Lecoutre
 */
public final class TableHybrid extends ExtensionStructure {

	@Override
	public boolean checkIndexes(int[] t) {
		for (HybridTuple hybridTuple : hybridTuples)
			if (hybridTuple.contains(t))
				return true;
		return false;
	}

	/**
	 * The set of hybrid/smart tuples/rows, each one being composed of a tuple subject to restrictions (unary, binary or ternary local constraints).
	 */
	public final HybridTuple[] hybridTuples;

	public TableHybrid(ConstraintExtension c, HybridTuple[] hybridTuples) {
		super(c);
		this.hybridTuples = hybridTuples;
	}

	@Override
	public void storeTuples(int[][] tuples, boolean positive) {
		throw new AssertionError("This method cannot be called because tuples are too different");
	}

	@Override
	public String toString() {
		return "Hybrid/Smart Tuples : " + Kit.join(hybridTuples);
	}

	/**********************************************************************************************
	 * Inner class for HybridTuple (and Restriction)
	 *********************************************************************************************/

	/**
	 * An hybrid tuple can be seen as a starred tuple subject to restrictions that represent local unary, binary or ternary constraints
	 */
	public static final class HybridTuple {

		/**
		 * The scope of the constraint on which the hybrid tuple is defined.
		 */
		private Variable[] scp;

		/**
		 * The tuple used as a basis for this hybrid tuple. It can contain stars and indexes (of values). Do note that it does not contain values (but indexes).
		 */
		private int[] tuple;

		/**
		 * The set of restrictions for this hybrid tuple
		 */
		private Restriction[] restrictions = new Restriction[0];

		/**
		 * The sparse sets used during filtering: nac[x] is the sparse set for indexes (of values) of x, which have not been found a support yet (nac stands for
		 * not arc-consistent).
		 */
		private SetSparse[] nac;

		/**
		 * Buffer used to store indexes (of values) in some methods
		 */
		private SetDense tmp;

		/**
		 * whichRestrictions[x] indicates the restriction where x occurs, or null if not present in any restriction.
		 */
		private Restriction[] whichRestrictions;

		/**
		 * The last time a validity check has been performed (may be useful to avoid some useless operations)
		 */
		private long valTime;

		/**
		 * The last time a support (collect) search has been performed (may be useful to avoid some useless operations)
		 */
		private long supTime;

		/**
		 * The tuple that is given initially. IMPORTANT: It contains values (and not indexes of values), but can also be null. This tuple is no more useful once
		 * the hybrid tuple is attached to its constraint.
		 */
		private int[] initialTuple;

		public static boolean isValid(AbstractTuple abstractTuple, IVar[] scp) {
			if (abstractTuple instanceof OrdinaryTuple) {
				int[] values = ((OrdinaryTuple) abstractTuple).values;
				for (int i = 0; i < values.length; i++)
					if (values[i] != STAR && ((Variable) scp[i]).dom.toIdx(values[i]) == -1)
						return false;
				return true;
			}
			Object[] values = ((AbstractTuple.HybridTuple) abstractTuple).values;
			for (int i = 0; i < values.length; i++)
				if (values[i] instanceof Integer && (Integer) values[i] != STAR && ((Variable) scp[i]).dom.toIdx((Integer) values[i]) == -1)
					return false;
			return true;
		}

		public static HybridTuple convert(AbstractTuple abstractTuple, IVar[] scp) {
			if (abstractTuple instanceof OrdinaryTuple)
				return new HybridTuple(((OrdinaryTuple) abstractTuple).values);
			Object[] values = ((AbstractTuple.HybridTuple) abstractTuple).values;
			int[] tuple = Kit.repeat(STAR, values.length);
			List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
			for (int i = 0; i < values.length; i++)
				if (values[i] instanceof Integer)
					tuple[i] = (Integer) values[i];
				else
					restrictions.add(Condition.toNode(scp[i], ((Condition) values[i])));
			return new HybridTuple(tuple, restrictions);
		}

		/**
		 * The restrictions that are given initially. Note that they correspond to Boolean tree expressions (for stating unary and binary local constraints).
		 * These expressions are no more useful once the hybrid tuple is attached to its constraint.
		 */
		private final List<XNodeParent<? extends IVar>> initialRestrictions;

		public HybridTuple(int[] tuple, List<XNodeParent<? extends IVar>> restrictions) {
			this.initialTuple = tuple;
			this.initialRestrictions = restrictions;
		}

		public HybridTuple(int[] tuple, Stream<XNodeParent<? extends IVar>> restrictions) {
			this(tuple, restrictions.collect(Collectors.toList()));
		}

		public HybridTuple(int[] tuple) {
			this(tuple, new ArrayList<>());
		}

		public HybridTuple(int[] tuple, XNodeParent<? extends IVar> restriction) {
			this(tuple, Arrays.asList(restriction));
		}

		public HybridTuple(int[] tuple, XNodeParent<? extends IVar> restriction1, XNodeParent<? extends IVar> restriction2) {
			this(tuple, Arrays.asList(restriction1, restriction2));
		}

		public HybridTuple(List<XNodeParent<? extends IVar>> restrictions) {
			this(null, restrictions);
		}

		public HybridTuple(Stream<XNodeParent<? extends IVar>> restrictions) {
			this(restrictions.collect(Collectors.toList()));
		}

		public HybridTuple(XNodeParent<? extends IVar> restriction) {
			this(Arrays.asList(restriction));
		}

		public HybridTuple(XNodeParent<? extends IVar> restriction1, XNodeParent<? extends IVar> restriction2) {
			this(Arrays.asList(restriction1, restriction2));
		}

		/**
		 * Builds a unary restriction of the form x <op> v
		 */
		private Restriction1Rel buildRestriction1From(int x, TypeConditionOperatorRel op, int v) {
			switch (op) {
			case LT:
				return new Rstr1LE(x, v, true);
			case LE:
				return new Rstr1LE(x, v, false);
			case GE:
				return new Rstr1GE(x, v, false);
			case GT:
				return new Rstr1GE(x, v, true);
			case EQ:
				return new Rstr1EQ(x, v);
			case NE:
				return new Rstr1NE(x, v);
			}
			throw new AssertionError();
		}

		/**
		 * Builds a unary restriction of the form x <op> {v1,v2, ...}
		 */
		private Restriction1 buildRestriction1From(int x, TypeConditionOperatorSet op, int[] t) {
			switch (op) {
			case IN:
				return new Rstr1IN(x, t);
			case NOTIN:
				return new Rstr1NOTIN(x, t);
			}
			throw new AssertionError();
		}

		/**
		 * Builds a binary restriction of the form x <op> y
		 */
		private Restriction2 buildRestriction2From(int x, TypeConditionOperatorRel op, int y) {
			if (scp[0].dom.typeIdentifier() != scp[1].dom.typeIdentifier())
				return buildRestriction2From(x, op, y, 0);
			switch (op) {
			case LT:
				return new Rstr2L(x, y, true);
			case LE:
				return new Rstr2L(x, y, false);
			case GE:
				return new Rstr2G(x, y, false);
			case GT:
				return new Rstr2G(x, y, true);
			case EQ:
				return new Rstr2EQ(x, y);
			case NE:
				return new Rstr2NE(x, y);
			}
			throw new AssertionError();
		}

		/**
		 * Builds a binary restriction of the form x <op> y + k
		 */
		private Restriction2 buildRestriction2From(int x, TypeConditionOperatorRel op, int y, int k) {
			if (k == 0 && scp[0].dom.typeIdentifier() == scp[1].dom.typeIdentifier())
				return buildRestriction2From(x, op, y);
			switch (op) {
			case GE:
				return new Rstr2GTVal(x, y, k - 1);
			case GT:
				return new Rstr2GTVal(x, y, k);
			case LT:
				return new Rstr2GTVal(y, x, -k);
			case LE:
				return new Rstr2GTVal(y, x, -k + 1);
			case EQ:
				return new Rstr2EQVal(x, y, k);
			default:
				throw new AssertionError("Currently, unimplemented operator " + op);
			}
		}

		/**
		 * Builds a ternary restriction of the form x >= y +/- z
		 */
		private Restriction3 buildRestriction3From(int x, TypeConditionOperatorRel op, int y, int z) {
			switch (op) {
			case EQ:
				return new Rstr3Add(x, y, z);
			default:
				throw new AssertionError("Currently, unimplemented operator " + op);
			}
		}

		private Restriction buildRestriction(int x, TypeExpr type, XNode<? extends IVar> son1) {
			if (type.oneOf(TypeExpr.IN, TypeExpr.NOTIN)) {
				if (son1.type == TypeExpr.SET) {
					int[] t = Stream.of(son1.sons).mapToInt(s -> safeInt((long) ((XNodeLeaf<?>) s).value)).toArray();
					return buildRestriction1From(x, type.toSetop(), t);
				}
				throw new AssertionError("Currently, unimplemented case for range (anyway, needs an extension of XCSP3)");
			}
			TypeConditionOperatorRel op = type.toRelop();
			control(op != null, "Relational operator expected");
			control(son1.type != TypeExpr.SYMBOL, "Symbolic values not possible for the moment");
			if (son1.type == TypeExpr.LONG) {
				int k = safeInt(((long) ((XNodeLeaf<?>) son1).value));
				if (op == EQ) {
					control(tuple[x] == STAR && scp[x].dom.containsValue(k));
					// for a constant, we directly put it in tuple (no need to build a Restriction object)
					tuple[x] = scp[x].dom.toIdx(k);
					return null;
				}
				Restriction1Rel res = buildRestriction1From(x, op, k);
				// TODO check cases that involve a restriction always false (and return an object mentioning it)
				if (res.pivot == -1 || res.pivot == Integer.MAX_VALUE) {
					control(tuple[x] == STAR);
					// return null; // AVOID THIS because in case of a restriction always false, the restriction would avoided ;; useless?
				}
				return res;
			}
			if (son1.type == TypeExpr.VAR) {
				int y = Utilities.indexOf(((XNodeLeaf<?>) son1).value, scp);
				control(tuple[y] == STAR);
				return buildRestriction2From(x, op, y);
			}
			if (son1.type == TypeExpr.PAR) {
				int y = (int) ((XNodeLeaf<?>) son1).value;
				control(tuple[y] == STAR);
				return buildRestriction2From(x, op, y);
			}
			control(son1.type.oneOf(TypeExpr.ADD, TypeExpr.SUB), son1 + " ");
			XNode<?>[] grandSons = ((XNodeParent<?>) son1).sons;
			control(grandSons.length == 2 && grandSons[0].type == TypeExpr.PAR);
			int y = (int) ((XNodeLeaf<?>) grandSons[0]).value;
			control(tuple[y] == STAR);
			if (grandSons[1].type == TypeExpr.LONG) {
				int k = safeInt(((long) ((XNodeLeaf<?>) grandSons[1]).value));
				return buildRestriction2From(x, op, y, son1.type == TypeExpr.ADD ? k : -k);
			}
			control(son1.type == TypeExpr.ADD && grandSons[1].type == TypeExpr.PAR);
			int z = (int) ((XNodeLeaf<?>) grandSons[1]).value;
			control(tuple[z] == STAR);
			return buildRestriction3From(x, op, y, z);
		}

		public void attach(CHybrid c) {
			this.scp = c.scp;
			this.initialTuple = initialTuple != null ? initialTuple : Kit.repeat(STAR, scp.length);
			this.tuple = IntStream.range(0, scp.length).map(i -> initialTuple[i] == STAR ? STAR : scp[i].dom.toIdx(initialTuple[i])).toArray();
			this.nac = c.nac;
			this.tmp = new SetDense(Stream.of(scp).mapToInt(x -> x.dom.initSize()).max().getAsInt());

			// Converting Boolean tree expressions into Restriction objects
			List<Restriction> list = new ArrayList<>();
			for (XNodeParent<? extends IVar> tree : initialRestrictions) {
				control(tree.sons.length == 2, tree.toString());
				TypeExpr type = tree.type;
				XNode<? extends IVar> son0 = tree.sons[0], son1 = tree.sons[1];
				if (son0.type != TypeExpr.VAR) {
					type = type.arithmeticInversion();
					control(type != null);
					son0 = tree.sons[1];
					son1 = tree.sons[0];
				}
				control(son0.type == TypeExpr.VAR, () -> "Left side operand must be a variable");
				int x = c.positionOf((Variable) ((XNodeLeaf<?>) son0).value);
				Restriction res = buildRestriction(x, type, son1);
				if (res != null)
					list.add(res);
			}
			// for each variable, we count the number of times it is seen at left (1), and at right (2) of the
			// restrictions
			int[] cnt1 = new int[scp.length], cnt2 = new int[scp.length];
			for (Restriction r : list) {
				cnt1[r.x]++;
				if (r instanceof Restriction2)
					cnt2[((Restriction2) r).y]++;
			}
			// for the moment, the code is valid for conditions below (we will extend the scope of hybrid tables later,
			// notably with multiple restrictions)
			// control(IntStream.range(0, scp.length).allMatch(i -> cnt1[i] + cnt2[i] <= 1));

			Map<Integer, List<Restriction>> byMainVariable = list.stream().collect(Collectors.groupingBy(r -> r.x));
			this.restrictions = byMainVariable.entrySet().stream()
					.map(e -> e.getValue().size() == 1 ? e.getValue().get(0) : new RestrictionMultiple(e.getKey(), e.getValue())).toArray(Restriction[]::new);

			this.whichRestrictions = new Restriction[scp.length];
			for (Restriction r : restrictions) {
				whichRestrictions[r.x] = r;
				if (r instanceof Restriction2)
					whichRestrictions[((Restriction2) r).y] = r;
				else if (r instanceof Restriction3) {
					whichRestrictions[((Restriction3) r).y] = r;
					whichRestrictions[((Restriction3) r).z] = r;
				} else if (r instanceof RestrictionMultiple)
					for (Restriction rr : ((RestrictionMultiple) r).subrestrictions)
						if (rr instanceof Restriction2)
							whichRestrictions[((Restriction2) rr).y] = r;
			}
			// System.out.println(this);
		}

		/**
		 * Returns true iff the the hybrid tuple "contains" the specified tuple of indexes
		 * 
		 * @param t
		 *            a tuple of indexes (of values)
		 * @return true iff the the hybrid tuple "contains" the specified tuple of indexes
		 */
		public final boolean contains(int[] t) {
			for (int i = 0; i < t.length; i++)
				if (tuple[i] != STAR && tuple[i] != t[i])
					return false;
			for (Restriction restriction : restrictions)
				if (!restriction.checkIndexes(t))
					return false;
			return true;
		}

		/**
		 * Returns true iff the the hybrid tuple is valid, considering the specified set of positions to check.
		 */
		public final boolean isValid(int[] sVal, int sValSize) {
			valTime++;
			for (int i = sValSize - 1; i >= 0; i--) {
				int x = sVal[i];
				int a = tuple[x];
				if (a != STAR && !scp[x].dom.contains(a))
					return false;
				Restriction restriction = whichRestrictions[x];
				if (restriction == null) {
					continue;
				} else if (restriction instanceof RestrictionComplex) {
					RestrictionComplex rc = (RestrictionComplex) restriction;
					if (rc.valTimeLocal != valTime) {
						rc.valTimeLocal = valTime; // updated because we make below the validity check
						if (restriction.isValid() == false)
							return false;
					}
				} else if (restriction.isValid() == false) {
					return false;
				}
				// if (restriction.valTimeLocal != valTime && !restriction.isValid())
				// return false;
			}
			return true;
		}

		/**
		 * Collect supported indexes for the specified set of positions to consider.
		 */
		public final int collect(int[] sSup, int sSupSize) {
			supTime++;
			for (int i = sSupSize - 1; i >= 0; i--) {
				int x = sSup[i];
				if (nac[x].isEmpty()) {
					sSup[i] = sSup[--sSupSize];
					continue; // may have been emptied (as second variable/position) when collecting on binary
								// restrictions
				}
				Restriction restriction = whichRestrictions[x];
				if (restriction == null) {
					int a = tuple[x];
					if (a == STAR)
						nac[x].clear();
					else
						nac[x].remove(a);
				} else if (restriction instanceof RestrictionComplex) {
					RestrictionComplex rc = (RestrictionComplex) restriction;
					if (rc.supTimeLocal != supTime) {
						rc.supTimeLocal = supTime; // updated because we make below the support searching (collect)
						restriction.collect();
					}
				} else
					restriction.collect();

				// if (restriction.supTimeLocal != supTime)
				// restriction.collect();
				if (nac[x].isEmpty())
					sSup[i] = sSup[--sSupSize];
			}
			return sSupSize;
		}

		@Override
		public String toString() {
			String s = "Hybrid tuple : " + (tuple == null ? "" : Kit.join(tuple, (Integer i) -> i == STAR ? "*" : i.toString()));
			boolean b = true;
			if (b)
				return s + " : " + Stream.of(restrictions).map(r -> r.toString() + " (" + r.getClass().getSimpleName() + ")").collect(Collectors.joining(", "));
			s += "\n  " + restrictions.length + " restrictons : ";
			for (Restriction r : restrictions)
				s += "\n    Restriction " + r.toString() + " ";
			for (int i = 0; i < whichRestrictions.length; i++)
				if (whichRestrictions[i] != null)
					s += "\n    " + scp[i] + " in restriction with vap " + whichRestrictions[i].x + " ";
			return s;
		}

		/**********************************************************************************************
		 * Root class for restrictions
		 *********************************************************************************************/

		/**
		 * A restriction always involves a variable whose value is ANY (*) in the initially underlying tuple
		 */
		public abstract class Restriction {

			/**
			 * The main variable (given by its position in the constraint scope) in the restriction (i.e., at the left side of the restriction)
			 */
			protected int x;

			/**
			 * The domain of x (redundant field)
			 */
			protected Domain domx;

			/**
			 * The sparse set for unsupported indexes of x (redundant field)
			 */
			protected SetSparse nacx;

			/**
			 * Returns true iff the restriction validates the specified tuple of indexes.
			 */
			public abstract boolean checkIndexes(int[] t);

			/**
			 * Returns true iff the restriction is valid (i.e., can still be satisfied).
			 */
			public abstract boolean isValid();

			/**
			 * Returns true iff the specified index (of value) for the variable x is valid, i.e. the restriction is valid for the smart tuple when x is set to
			 * (the value for) a
			 * 
			 * @param a
			 *            an index (of value)
			 * @return true iff the specified index (of value) for the variable x is valid
			 */
			public abstract boolean isValidFor(int a);

			/**
			 * Updates information about supported indexes (i.e., updates the structure nac)
			 */
			public abstract void collect();

			/**
			 * Builds a restriction whose main variable (left-hand side) is the specified variable
			 * 
			 * @param x
			 *            the main variable of the restriction
			 */
			protected Restriction(int x) {
				this.x = x;
				this.domx = scp[x].dom;
				this.nacx = nac[x];
				control(tuple[x] == STAR, () -> getClass().getName() + " " + Kit.join(tuple));
			}
		}

		/**********************************************************************************************
		 * Classes for unary restrictions of the form x <op> v
		 *********************************************************************************************/

		/**
		 * Unary restriction that can be based on a relational operator or a set operator.
		 */
		abstract class Restriction1 extends Restriction {

			@Override
			public boolean checkIndexes(int[] t) {
				return isValidFor(t[x]); // we can call isValidFor because the restriction is unary
			}

			protected Restriction1(int x) {
				super(x);
			}
		}

		/**
		 * Unary restriction based on a relational operator, i.e., of the form x <op> v with <op> in {lt,le,ge,gt,ne,eq}. We reason with indexes by computing
		 * the relevant index called pivot: this is the index of the value in dom(x) that is related to v ; see subclass constructors for details).
		 */
		abstract class Restriction1Rel extends Restriction1 {

			/**
			 * The operator involved in the unary restriction
			 */
			private TypeConditionOperatorRel op;

			/**
			 * The index of the value in the domain of x that is related to the value v (that can be seen as a limit) specified at construction in subclasses
			 */
			protected int pivot;

			protected Restriction1Rel(int x, TypeConditionOperatorRel op, int pivot) {
				super(x);
				this.op = op;
				this.pivot = pivot;
				// control(pivot != -1 && pivot != Integer.MAX_VALUE,
				// () -> "useless restriction if the pivot cannot be computed (and correspond to an index of value)");
			}

			@Override
			public String toString() {
				return scp[x] + " " + op + " " + scp[x].dom.toVal(pivot);
			}
		}

		/**
		 * Restriction of the form x <= v, or x < v (when strict)
		 */
		final class Rstr1LE extends Restriction1Rel {

			protected Rstr1LE(int x, int v, boolean strict) {
				super(x, LE, Domain.greatestIndexOfValueLessThan(scp[x].dom, v, strict));
			}

			@Override
			public boolean isValid() {
				return domx.first() <= pivot;
			}

			@Override
			public boolean isValidFor(int a) {
				return a <= pivot;
			}

			@Override
			public void collect() {
				// three ways of collecting
				int nValid = pivot - domx.first(), nInvalid = domx.last() - pivot; // numbers are rough approximations
				if (nInvalid < nValid && nInvalid < nacx.size()) {
					tmp.clear();
					for (int a = domx.last(); a != -1 && a > pivot; a = domx.prev(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				} else if (nValid < nacx.size()) {
					for (int a = domx.first(); a != -1 && a <= pivot; a = domx.next(a))
						nacx.remove(a);
				} else
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (a <= pivot)
							nacx.remove(a);
					}
			}

		}

		/**
		 * Restriction of the form x >= v, or x > v when strict
		 */
		final class Rstr1GE extends Restriction1Rel {

			protected Rstr1GE(int x, int v, boolean strict) {
				super(x, GE, Domain.smallestIndexOfValueGreaterThan(scp[x].dom, v, strict));
			}

			@Override
			public boolean isValid() {
				return domx.last() >= pivot;
			}

			@Override
			public boolean isValidFor(int a) {
				return a >= pivot;
			}

			@Override
			public void collect() {
				// three ways of collecting
				int nValid = domx.last() - pivot, nInvalid = pivot - domx.first(); // numbers are rough approximations
				if (nInvalid < nValid && nInvalid < nacx.size()) {
					tmp.clear();
					for (int a = domx.first(); a != -1 && a < pivot; a = domx.next(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				} else if (nValid < nacx.size()) {
					for (int a = domx.last(); a != -1 && a >= pivot; a = domx.prev(a))
						nacx.remove(a);
				} else
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (a >= pivot)
							nacx.remove(a);
					}
			}

		}

		/**
		 * Restriction of the form x != v
		 */
		final class Rstr1NE extends Restriction1Rel {

			protected Rstr1NE(int x, int v) {
				super(x, NE, scp[x].dom.toIdx(v));
			}

			protected Rstr1NE(int x, String v) {
				super(x, NE, ((DomainSymbols) scp[x].dom).toIdx(v));
			}

			@Override
			public boolean isValid() {
				return domx.size() > 1 || domx.single() != pivot;
			}

			@Override
			public boolean isValidFor(int a) {
				return a != pivot;
			}

			@Override
			public void collect() {
				if (nacx.contains(pivot))
					nacx.resetTo(pivot);
				else
					nacx.clear();
			}
		}

		/**
		 * Restriction of the form x == v
		 */
		final class Rstr1EQ extends Restriction1Rel {

			protected Rstr1EQ(int x, int v) {
				super(x, EQ, scp[x].dom.toIdx(v));
			}

			protected Rstr1EQ(int x, String v) {
				super(x, EQ, ((DomainSymbols) scp[x].dom).toIdx(v));
			}

			@Override
			public boolean isValid() {
				return domx.contains(pivot);
			}

			@Override
			public boolean isValidFor(int a) {
				return a == pivot;
			}

			@Override
			public void collect() {
				nacx.remove(pivot); // not a problem to call remove if the pivot is not present
			}
		}

		/**
		 * Unary restriction based on a set operator, i.e., of the form x <op> {v1, v2, ...} with <op> in {in, notin}. Note that we reason with indexes of
		 * values (and not directly with values).
		 */
		abstract class Restriction1Set extends Restriction1 {

			/**
			 * The operator in the unary restriction
			 */
			private TypeConditionOperatorSet op;

			/**
			 * The set of indexes corresponding to values initially specified at construction
			 */
			protected Set<Integer> set;

			protected Restriction1Set(int x, TypeConditionOperatorSet op, int[] values) {
				super(x);
				this.op = op;
				this.set = IntStream.of(values).mapToObj(v -> domx.toIdx(v)).filter(v -> v >= 0).collect(Collectors.toCollection(TreeSet::new));
				assert set.size() >= 1 && Kit.isStrictlyIncreasing(values);
			}

			@Override
			public String toString() {
				return scp[x] + " " + op + " {" + set.stream().map(a -> domx.toVal(a) + "").collect(Collectors.joining(",")) + "}";
			}
		}

		/**
		 * Restriction of the form x in {v1, v2, ...}
		 */
		final class Rstr1IN extends Restriction1Set {

			private int residue; // last found index that was present in domx and supports

			protected Rstr1IN(int x, int[] supports) {
				super(x, IN, supports);
				this.residue = set.iterator().next(); // first index of value used as residue
			}

			@Override
			public boolean isValid() {
				if (domx.contains(residue))
					return true;
				if (set.size() <= domx.size())
					for (int a : set) {
						if (domx.contains(a)) {
							residue = a;
							return true;
						}
					}
				else
					for (int a = domx.first(); a != -1; a = domx.next(a))
						if (set.contains(a)) {
							residue = a;
							return true;
						}
				return false;
			}

			@Override
			public boolean isValidFor(int a) {
				return set.contains(a);
			}

			@Override
			public void collect() {
				if (set.size() <= nacx.size())
					for (int a : set) {
						if (nacx.contains(a))
							nacx.remove(a);
					}
				else
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (set.contains(a))
							nacx.remove(a);
					}
			}
		}

		/**
		 * Restriction of the form x not in {v1, v2, ...}
		 */
		final class Rstr1NOTIN extends Restriction1Set {

			private int residue; // last found index that was present in domx and absent from conflicts

			protected Rstr1NOTIN(int x, int[] conflicts) {
				super(x, NOTIN, conflicts);
				this.residue = -1;
				for (int a = domx.first(); residue == -1 && a != -1; a = domx.next(a))
					if (!set.contains(a))
						residue = a;
				control(residue != -1);
			}

			@Override
			public boolean isValid() {
				if (domx.contains(residue))
					return true;
				for (int a = domx.first(); a != -1; a = domx.next(a))
					if (!set.contains(a)) {
						residue = a;
						return true;
					}
				return false;
			}

			@Override
			public boolean isValidFor(int a) {
				return !set.contains(a);
			}

			@Override
			public void collect() {
				if (domx.size() <= nacx.size()) {
					// TODO is that useful? don't we always have nacx smaller than domx by initialization?
					for (int a = domx.first(); a != -1; a = domx.next(a))
						if (nacx.contains(a) && !set.contains(a))
							nacx.remove(a);
				} else
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (!set.contains(a))
							nacx.remove(a);
					}
			}
		}

		/**********************************************************************************************
		 * Classes for binary restrictions of the form x <op> y
		 *********************************************************************************************/

		// TODO can we systematically iterate over nacx instead of domx because it is always a smaller set????

		abstract class RestrictionComplex extends Restriction {
			protected long valTimeLocal, supTimeLocal;

			protected RestrictionComplex(int x) {
				super(x);
			}
		}

		/**
		 * Binary restriction based on a relational operator, i.e. the form x <op> y
		 */
		abstract class Restriction2 extends RestrictionComplex {

			/**
			 * The operator involved in the binary restriction
			 */
			protected TypeConditionOperatorRel op;

			/**
			 * The second variable (given by its position in the constraint scope) in the restriction (i.e., at the right side of the restriction)
			 */
			protected int y;

			/**
			 * The domain of y (redundant field)
			 */
			protected Domain domy;

			/**
			 * The sparse set for unsupported indexes of y (redundant field)
			 */
			protected SetSparse nacy;

			protected int nSupportlessValues() {
				return nacx.size() + nacy.size();
			}

			protected Restriction2(int x, TypeConditionOperatorRel op, int y) {
				super(x);
				this.op = op;
				this.y = y;
				this.domy = scp[y].dom;
				this.nacy = nac[y];
				control(x != y,
						"Bad form for a binary restriction of a hybrid tuple: two occurrences of the same variable: " + scp[x] + " " + op + " " + scp[y]);
				// control(domx.typeIdentifier() == domy.typeIdentifier() || this instanceof Rstr2EQVal);
			}

			/**
			 * Method called when the backward phase of a RestrictionMultiple object has been performed. More precisely, in tmp, we have the indexes (of values)
			 * for scope[x] that are compatible with all subrestrictions of the RestrictionMultiple. We call this method to perform the forward phase.
			 */
			public abstract void collectForY();

		}

		abstract class Restriction2Idx extends Restriction2 {

			protected Restriction2Idx(int x, TypeConditionOperatorRel op, int y) {
				super(x, op, y);
				control(domx.typeIdentifier() == domy.typeIdentifier());
			}

			@Override
			public String toString() {
				return scp[x] + " " + op + " " + scp[y];
			}
		}

		/**
		 * Restriction of the form x < y (when strict) or x <= y
		 */
		final class Rstr2L extends Restriction2Idx {

			@Override
			public boolean checkIndexes(int[] t) {
				return strict ? t[x] < t[y] : t[x] <= t[y];
			}

			private boolean strict;

			protected Rstr2L(int x, int y, boolean strict) {
				super(x, strict ? LT : LE, y);
				this.strict = strict;
			}

			@Override
			public boolean isValid() {
				return strict ? domx.first() < domy.last() : domx.first() <= domy.last();
			}

			@Override
			public boolean isValidFor(int a) {
				return strict ? a < domy.last() : a <= domy.last();
			}

			private void collectThroughInvalidValues() {
				int firstx = domx.first(), lasty = domy.last();
				if (!scp[x].assigned()) {
					tmp.clear();
					for (int a = domx.last(); a != -1 && (strict ? a >= lasty : a > lasty); a = domx.prev(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				}
				if (!scp[y].assigned()) {
					tmp.clear();
					for (int b = domy.first(); b != -1 && (strict ? firstx >= b : firstx > b); b = domy.next(b))
						if (nacy.contains(b))
							tmp.add(b);
					nacy.resetTo(tmp);
				}
			}

			private void collectThroughSupportlessSets() {
				int firstx = domx.first(), lasty = domy.last();
				if (!scp[x].assigned())
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (strict ? a < lasty : a <= lasty)
							nacx.remove(a);
					}
				if (!scp[y].assigned())
					for (int i = nacy.limit; i >= 0; i--) {
						int b = nacy.dense[i];
						if (strict ? firstx < b : firstx <= b)
							nacy.remove(b);
					}
			}

			private void collectThroughValidValues() {
				int firstx = domx.first(), lasty = domy.last();
				if (!scp[x].assigned())
					for (int a = domx.first(); a != -1 && (strict ? a < lasty : a <= lasty); a = domx.next(a))
						nacx.remove(a);
				if (!scp[y].assigned())
					for (int b = domy.last(); b != -1 && (strict ? firstx < b : firstx <= b); b = domy.prev(b))
						nacy.remove(b);
			}

			@Override
			public void collect() {
				// 2(+1) parameters (approximations of the true numbers) for choosing the cheapest way of collecting
				int nInvalid = Math.max(domx.first() - domy.first(), 0) + Math.max(domx.last() - domy.last(), 0);
				int nValid = Math.min(domx.last(), domy.last()) - domx.first() + domy.last() - Math.max(domx.first(), domy.first());
				if (nInvalid < nSupportlessValues() && nInvalid < nValid)
					collectThroughInvalidValues();
				else if (nSupportlessValues() < nValid)
					collectThroughSupportlessSets();
				else
					collectThroughValidValues();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned()) {
					int first = tmp.first();
					for (int b = domy.last(); b != -1 && (strict ? first < b : first <= b); b = domy.prev(b))
						nacy.remove(b);
				}
			}
		}

		/**
		 * Restriction of the form x > y (when strict) or x >= y
		 */
		final class Rstr2G extends Restriction2Idx {

			@Override
			public boolean checkIndexes(int[] t) {
				return strict ? t[x] > t[y] : t[x] >= t[y];
			}

			private boolean strict;

			protected Rstr2G(int x, int y, boolean strict) {
				super(x, strict ? GT : GE, y);
				this.strict = strict;
			}

			@Override
			public boolean isValid() {
				return strict ? domx.last() > domy.first() : domy.last() >= domy.first();
			}

			@Override
			public boolean isValidFor(int a) {
				return strict ? a > domy.first() : a >= domy.first();
			}

			private void collectThroughInvalidValues() {
				int lastx = domx.last(), firsty = domy.first();
				if (!scp[x].assigned()) {
					tmp.clear();
					for (int a = domx.first(); a != -1 && (strict ? a <= firsty : a < firsty); a = domx.next(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				}
				if (!scp[y].assigned()) {
					tmp.clear();
					for (int b = domy.last(); b != -1 && (strict ? b >= lastx : b > lastx); b = domy.prev(b))
						if (nacy.contains(b))
							tmp.add(b);
					nacy.resetTo(tmp);
				}
			}

			private void collectThroughSupportlessSets() {
				int lastx = domx.last(), firsty = domy.first();
				if (!scp[x].assigned())
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (strict ? a > firsty : a >= firsty)
							nacx.remove(a);
					}
				if (!scp[y].assigned())
					for (int i = nacy.limit; i >= 0; i--) {
						int b = nacy.dense[i];
						if (strict ? lastx > b : lastx >= b)
							nacy.remove(b);
					}
			}

			private void collectThroughValidValues() {
				int lastx = domx.last(), firsty = domy.first();
				if (!scp[x].assigned())
					for (int a = domx.last(); a != -1 && (strict ? a > firsty : a >= firsty); a = domx.prev(a))
						nacx.remove(a);
				if (!scp[y].assigned())
					for (int b = domy.first(); b != -1 && (strict ? lastx > b : lastx >= b); b = domy.next(b))
						nacy.remove(b);
			}

			@Override
			public void collect() {
				// 2(+1) parameters (approximations of the true numbers) for choosing the cheapest way of collecting
				int nInvalid = Math.max(domy.first() - domx.first(), 0) + Math.max(domy.last() - domx.last(), 0);
				int nValid = Math.min(domx.last(), domy.last()) - domy.first() + domx.last() - Math.max(domx.first(), domy.first());
				if (nInvalid < nSupportlessValues() && nInvalid < nValid)
					collectThroughInvalidValues();
				else if (nSupportlessValues() < nValid)
					collectThroughSupportlessSets();
				else
					collectThroughValidValues();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned()) {
					int last = tmp.last();
					for (int b = domy.first(); b != -1 && (strict ? last > b : last >= b); b = domy.next(b))
						nacy.remove(b);
				}
			}

		}

		/**
		 * Restriction of the form x != y
		 */
		final class Rstr2NE extends Restriction2Idx {

			@Override
			public boolean checkIndexes(int[] t) {
				return t[x] != t[y];
			}

			protected Rstr2NE(int x, int y) {
				super(x, NE, y);
			}

			@Override
			public boolean isValid() {
				return domx.size() > 1 || domy.size() > 1 || domx.single() != domy.single();
			}

			@Override
			public boolean isValidFor(int a) {
				return domy.size() > 1 || a != domy.single();
			}

			@Override
			public void collect() {
				if (!scp[x].assigned())
					if (domy.size() == 1 && nacx.contains(domy.single()))
						nacx.resetTo(domy.single());
					else
						nacx.clear();
				if (!scp[y].assigned())
					if (domx.size() == 1 && nacy.contains(domx.single()))
						nacy.resetTo(domx.single());
					else
						nacy.clear();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned()) {
					int first = tmp.first();
					if (tmp.size() == 1 && nacy.contains(first))
						nacy.resetTo(first);
					else
						nacy.clear();
				}
			}
		}

		/**
		 * Restriction of the form x = y
		 */
		final class Rstr2EQ extends Restriction2Idx {

			@Override
			public boolean checkIndexes(int[] t) {
				return t[x] == t[y];
			}

			private int residue;

			private boolean newResidue;

			protected Rstr2EQ(int x, int y) {
				super(x, EQ, y);
				control(domx.typeIdentifier() == domy.typeIdentifier());
			}

			@Override
			public boolean isValidFor(int a) {
				return domy.contains(a);
			}

			@Override
			public boolean isValid() {
				newResidue = false;
				if (domx.contains(residue) && domy.contains(residue))
					return true;
				newResidue = true;
				Domain small = domx.size() < domy.size() ? domx : domy, large = small == domx ? domy : domx;
				for (int a = small.first(); a != -1; a = small.next(a))
					if (large.contains(a)) {
						residue = a;
						return true;
					}
				return false;
			}

			private void collectThroughRemovedValues() {
				if (!scp[x].assigned()) {
					tmp.clear();
					for (int a = domy.lastRemoved(); a != -1; a = domy.prevRemoved(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				}
				if (!scp[y].assigned()) {
					tmp.clear();
					for (int a = domx.lastRemoved(); a != -1; a = domx.prevRemoved(a))
						if (nacy.contains(a))
							tmp.add(a);
					nacy.resetTo(tmp);
				}
			}

			private void collectThroughSmallestDomain() {
				Domain small = domx.size() < domy.size() ? domx : domy, large = small == domx ? domy : domx;
				int start = valTimeLocal == valTime && newResidue ? residue : small.first();
				// above, are we sure that the smallest domain is the same (no removal between? it seems so)
				if (scp[x].assigned() || scp[y].assigned()) {
					assert small.single() == start;
					if (large.contains(start)) {
						if (!scp[x].assigned())
							nacx.remove(start);
						if (!scp[y].assigned())
							nacy.remove(start);
					}
				} else {
					for (int a = start; a != -1; a = small.next(a))
						if (large.contains(a)) {
							nacx.remove(a);
							nacy.remove(a);
						}
				}
			}

			private void collectThroughSupportlessSets() {
				if (!scp[x].assigned())
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (domy.contains(a))
							nacx.remove(a);
					}
				if (!scp[y].assigned())
					for (int i = nacy.limit; i >= 0; i--) {
						int a = nacy.dense[i];
						if (domx.contains(a))
							nacy.remove(a);
					}
			}

			@Override
			public void collect() {
				// three parameters for choosing the cheapest way of collecting
				int nRemoved = domx.nRemoved() + domy.nRemoved();
				int minDomainSize = Math.min(domx.size(), domy.size());
				if (nRemoved < nSupportlessValues() && nRemoved < minDomainSize)
					collectThroughRemovedValues();
				else if (nSupportlessValues() < minDomainSize)
					collectThroughSupportlessSets();
				else
					collectThroughSmallestDomain();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned())
					nacy.removeAll(tmp);
			}

		}

		abstract class Restriction2Val extends Restriction2 {

			protected int k;

			protected Restriction2Val(int x, TypeConditionOperatorRel op, int y, int k) {
				super(x, op, y);
				this.k = k;
			}

			@Override
			public String toString() {
				return scp[x] + " " + op + " " + scp[y] + (k != 0 ? " + " + k : "");
			}
		}

		/**
		 * Restriction of the form x = y + k
		 */
		final class Rstr2EQVal extends Restriction2Val {

			@Override
			public boolean checkIndexes(int[] t) {
				return domx.toVal(t[x]) == domy.toVal(t[y]) + k;
			}

			private int valResidue;

			protected Rstr2EQVal(int x, int y, int k) {
				super(x, EQ, y, k);
			}

			@Override
			public boolean isValidFor(int a) {
				return domy.toIdxIfPresent(domx.toVal(a) - k) != -1;
			}

			@Override
			public boolean isValid() {
				if (domx.containsValue(valResidue) && domy.containsValue(valResidue - k))
					return true;
				Domain small = domx.size() < domy.size() ? domx : domy, large = small == domx ? domy : domx;
				int kk = small == domx ? -k : k;
				for (int a = small.first(); a != -1; a = small.next(a)) {
					int v = small.toVal(a);
					if (large.containsValue(v + kk)) {
						valResidue = small == domx ? v : v + k;
						return true;
					}
				}
				return false;
			}

			private void collectThroughRemovedValues() {
				if (!scp[x].assigned()) {
					tmp.clear();
					for (int a = domy.lastRemoved(); a != -1; a = domy.prevRemoved(a)) {
						int v = domy.toVal(a) + k;
						int b = domx.toIdxIfPresent(v);
						if (b != -1 && nacx.contains(b))
							tmp.add(b);
					}
					nacx.resetTo(tmp);
				}
				if (!scp[y].assigned()) {
					tmp.clear();
					for (int a = domx.lastRemoved(); a != -1; a = domx.prevRemoved(a)) {
						int v = domx.toVal(a) - k;
						int b = domy.toIdxIfPresent(v);
						if (b != -1 && nacy.contains(b))
							tmp.add(b);
					}
					nacy.resetTo(tmp);
				}
			}

			private void collectThroughSmallestDomain() {
				Domain small = domx.size() < domy.size() ? domx : domy, large = small == domx ? domy : domx;
				int kk = small == domx ? -k : k;
				if (!scp[x].assigned() && !scp[y].assigned()) {
					for (int a = small.first(); a != -1; a = small.next(a)) {
						int v = small.toVal(a) + kk;
						int b = large.toIdxIfPresent(v);
						if (b != -1) {
							nacx.remove(small == domx ? a : b);
							nacy.remove(small == domx ? b : a);
						}
					}
				} else if (!scp[x].assigned()) {
					for (int a = small.first(); a != -1; a = small.next(a)) {
						int v = small.toVal(a) + kk;
						int b = large.toIdxIfPresent(v);
						if (b != -1)
							nacx.remove(small == domx ? a : b);
					}
				} else if (!scp[y].assigned()) {
					for (int a = small.first(); a != -1; a = small.next(a)) {
						int v = small.toVal(a) + kk;
						int b = large.toIdxIfPresent(v);
						if (b != -1)
							nacy.remove(small == domx ? b : a);
					}
				}
			}

			private void collectThroughSupportlessSets() {
				if (!scp[x].assigned())
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (domy.containsValue(domx.toVal(a) - k))
							nacx.remove(a);
					}
				if (!scp[y].assigned())
					for (int i = nacy.limit; i >= 0; i--) {
						int a = nacy.dense[i];
						if (domx.containsValue(domy.toVal(a) + k))
							nacy.remove(a);
					}
			}

			@Override
			public void collect() {
				// three parameters for choosing the cheapest way of collecting
				int nRemoved = domx.nRemoved() + domy.nRemoved();
				int minDomainSize = Math.min(domx.size(), domy.size());
				if (nRemoved < nSupportlessValues() && nRemoved < minDomainSize)
					collectThroughRemovedValues();
				else if (nSupportlessValues() < minDomainSize)
					collectThroughSupportlessSets();
				else
					collectThroughSmallestDomain();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned())
					for (int i = 0; i < tmp.size(); i++) {
						int a = tmp.dense[i];
						int v = domx.toVal(a) - k;
						assert domy.containsValue(v);
						nacy.remove(domy.toIdx(v));
					}
			}
		}

		/**
		 * Restriction of the form x > y + k
		 */
		final class Rstr2GTVal extends Restriction2Val {

			@Override
			public boolean checkIndexes(int[] t) {
				return domx.toVal(t[x]) > domy.toVal(t[y]) + k;
			}

			protected Rstr2GTVal(int x, int y, int k) {
				super(x, GT, y, k);
			}

			@Override
			public boolean isValidFor(int a) {
				return domx.toVal(a) > domy.firstValue() + k;
			}

			@Override
			public boolean isValid() {
				return domx.lastValue() > domy.firstValue() + k;
			}

			private void collectThroughInvalidValues() {
				if (!scp[x].assigned()) {
					int limit = domy.firstValue() + k;
					tmp.clear();
					for (int a = domx.first(); a != -1 && domx.toVal(a) <= limit; a = domx.next(a))
						if (nacx.contains(a))
							tmp.add(a);
					nacx.resetTo(tmp);
				}
				if (!scp[y].assigned()) {
					int limit = domx.lastValue() - k;
					tmp.clear();
					for (int b = domy.last(); b != -1 && domy.toVal(b) >= limit; b = domy.prev(b))
						if (nacy.contains(b))
							tmp.add(b);
					nacy.resetTo(tmp);
				}
			}

			private void collectThroughSupportlessSets() {
				if (!scp[x].assigned()) {
					int limit = domy.firstValue() + k;
					for (int i = nacx.limit; i >= 0; i--) {
						int a = nacx.dense[i];
						if (domx.toVal(a) > limit)
							nacx.remove(a);
					}
				}
				if (!scp[y].assigned()) {
					int limit = domx.lastValue() - k;
					for (int i = nacy.limit; i >= 0; i--) {
						int b = nacy.dense[i];
						if (domy.toVal(b) < limit)
							nacy.remove(b);
					}
				}
			}

			private void collectThroughValidValues() {
				if (!scp[x].assigned()) {
					int limit = domy.firstValue() + k;
					for (int a = domx.last(); a != -1 && domx.toVal(a) > limit; a = domx.prev(a))
						nacx.remove(a);
				}
				if (!scp[y].assigned()) {
					int limit = domx.lastValue() - k;
					for (int b = domy.first(); b != -1 && domy.toVal(b) < limit; b = domy.next(b))
						nacy.remove(b);
				}
			}

			@Override
			public void collect() {
				// three parameters for choosing the cheapest way of collecting
				int nInvalid = Math.max(domy.firstValue() + k - domx.firstValue(), 0) + Math.max(domy.lastValue() + k - domx.lastValue(), 0);
				int nValid = Math.min(domx.lastValue(), domy.lastValue()) + k - domy.firstValue() + domx.lastValue()
						- Math.max(domx.firstValue(), domy.firstValue() + k);
				if (nInvalid < nSupportlessValues() && nInvalid < nValid)
					collectThroughInvalidValues();
				else if (nSupportlessValues() < nValid)
					collectThroughSupportlessSets();
				else
					collectThroughValidValues();
			}

			@Override
			public void collectForY() {
				if (!scp[y].assigned()) {
					int limit = domx.toVal(tmp.last()) - k;
					for (int b = domy.first(); b != -1 && domy.toVal(b) < limit; b = domy.next(b))
						nacy.remove(b);
				}
			}
		}

		/**********************************************************************************************
		 * Classes for ternary restrictions of the form x <op> y +/- z
		 *********************************************************************************************/

		/**
		 * Ternary restriction based on a relational operator, i.e. the form x <op> y +/- y
		 */
		abstract class Restriction3 extends RestrictionComplex {

			/**
			 * The operator involved in the ternary restriction
			 */
			protected TypeConditionOperatorRel op;

			/**
			 * The second variable (given by its position in the constraint scope) in the restriction (i.e., at the right side of the restriction)
			 */
			protected int y;

			/**
			 * The domain of y (redundant field)
			 */
			protected Domain domy;

			/**
			 * The third variable (given by its position in the constraint scope) in the restriction (i.e., at the right side of the restriction)
			 */
			protected int z;

			/**
			 * The domain of z (redundant field)
			 */
			protected Domain domz;

			/**
			 * The sparse set for unsupported indexes of y (redundant field)
			 */
			protected SetSparse nacy;

			/**
			 * The sparse set for unsupported indexes of z (redundant field)
			 */
			protected SetSparse nacz;

			protected Restriction3(int x, TypeConditionOperatorRel op, int y, boolean addition, int z) {
				super(x);
				this.op = op;
				this.y = y;
				this.domy = scp[y].dom;
				this.nacy = nac[y];
				this.z = z;
				this.domz = scp[z].dom;
				this.nacz = nac[z];
				// control(domx.typeIdentifier() == domy.typeIdentifier() || this instanceof Rstr2EQVal);
				control(x != y && x != z && y != z, "Bad form for a ternary restriction of a hybrid tuple: two occurrences of the same variable: " + scp[x]
						+ " " + op + " " + scp[y] + (addition ? "+" : "-") + scp[z]);
			}

			@Override
			public String toString() {
				return scp[x] + " " + op + " " + scp[y] + (this instanceof Rstr3Add ? "+" : "<op>") + scp[z];
			}
		}

		/**
		 * Restriction of the form x = y + z
		 */
		final class Rstr3Add extends Restriction3 {

			@Override
			public boolean checkIndexes(int[] t) {
				return t[x] == t[y] + t[z];
			}

			protected Rstr3Add(int x, int y, int z) {
				super(x, EQ, y, true, z);
				// System.out.println("building " + this);
			}

			@Override
			public boolean isValidFor(int a) {
				return false; // TODO
			}

			@Override
			public boolean isValid() {
				throw new AssertionError("Not implemented");
			}

			@Override
			public void collect() {
				// TODO
			}
		}

		/**********************************************************************************************
		 * Classes for restrictions of the form x <op1> y and x <op2> z ...
		 *********************************************************************************************/

		/**
		 * Restriction of the form of a conjunction of constraints: x <op1> y and x <op2> z ... with x the main common variable
		 */
		final class RestrictionMultiple extends RestrictionComplex {

			/**
			 * The restrictions involved in this multiple restriction. All involved restrictions are on the same main variable.
			 */
			protected Restriction[] subrestrictions;

			protected RestrictionMultiple(int x, List<Restriction> restrictions) {
				super(x);
				this.subrestrictions = restrictions.toArray(new Restriction[restrictions.size()]);
				assert restrictions.size() > 1;
				// for the moment, restriction3 not considered
				assert Stream.of(subrestrictions).allMatch(r -> r.x == x && !(r instanceof RestrictionMultiple) && !(r instanceof Restriction3));
			}

			@Override
			public boolean isValidFor(int a) {
				for (Restriction restriction : subrestrictions)
					if (!restriction.isValidFor(a))
						return false;
				return true;
			}

			@Override
			public boolean isValid() {
				// we collect in tmp the valid indexes (of values) for x
				tmp.clear();
				for (int a = domx.first(); a != -1; a = domx.next(a))
					if (isValidFor(a))
						tmp.add(a);
				return tmp.size() > 0;
			}

			@Override
			public void collect() {
				if (valTimeLocal != valTime) { // TODO is that possible?
					boolean valid = isValid();
					assert valid;
				}
				// we update nacx from indexes stored in tmp
				if (!scp[x].assigned())
					nacx.removeAll(tmp);
				// we update the nac sets for the other involved variables
				for (Restriction restriction : subrestrictions)
					if (restriction instanceof Restriction2)
						((Restriction2) restriction).collectForY();
			}

			@Override
			public boolean checkIndexes(int[] t) {
				for (Restriction restriction : subrestrictions)
					if (!restriction.checkIndexes(t))
						return false;
				return true;
			}

			@Override
			public String toString() {
				return Stream.of(subrestrictions).map(r -> r.toString()).collect(Collectors.joining(", "));
			}
		}

	}

}
