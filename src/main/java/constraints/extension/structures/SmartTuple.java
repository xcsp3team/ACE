package constraints.extension.structures;

import static org.xcsp.common.Constants.STAR;
import static org.xcsp.common.Types.TypeConditionOperatorRel.EQ;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.GT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LE;
import static org.xcsp.common.Types.TypeConditionOperatorRel.LT;
import static org.xcsp.common.Types.TypeConditionOperatorRel.NE;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.Types;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;

import constraints.extension.ExtensionSmart;
import sets.SetSparse;
import utility.Kit;
import variables.Domain;
import variables.DomainInteger.DomainRange;
import variables.DomainInteger.DomainSymbols;
import variables.Variable;

public final class SmartTuple {

	/** The scope of the constraint on which the smart tuple is defined. */
	private Variable[] scp;

	/** The tuple serving as basis for this smart tuple. */
	public int[] prefixWithValues;

	/** The tuple serving as basis for this smart tuple, with indices instead of values. */
	public int[] prefix;

	/** The set of restrictions associated with this smart tuple. */
	private RestrictionSimple[] restrictions;

	/** supportlesss[x] gives the sparse set of idxs for which no support has been found yet. */
	private SetSparse[] supportlesss;

	/** Temporary array to store idxs used in some collecting methods. */
	private int[] tmp;

	/** whichRestrictions[x] indicates the restriction where x occurs (it may correspond to either vap or vap2), or null. */
	private RestrictionSimple[] whichRestrictions;

	/** Time counters used to avoid useless redundant operations. */
	private long valTime, supTime;

	public final List<XNodeParent<? extends IVar>> collectedTreeRestrictions;

	// private int[] unrestrictedStars;
	// private int[] unrestrictedIdxs;

	public SmartTuple(int[] tuple, List<XNodeParent<? extends IVar>> restrictions) {
		this.prefixWithValues = tuple;
		this.collectedTreeRestrictions = restrictions;
	}

	public SmartTuple(int[] tuple, Stream<XNodeParent<? extends IVar>> restrictions) {
		this(tuple, restrictions.collect(Collectors.toList()));
	}

	public SmartTuple(int[] tuple) {
		this(tuple, new ArrayList<>());
	}

	public SmartTuple(int[] tuple, XNodeParent<? extends IVar> r) {
		this(tuple, Arrays.asList(r));
	}

	public SmartTuple(int[] tuple, XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2) {
		this(tuple, Arrays.asList(r1, r2));
	}

	public SmartTuple(int[] tuple, XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2, XNodeParent<? extends IVar> r3) {
		this(tuple, Arrays.asList(r1, r2, r3));
	}

	public SmartTuple(int[] tuple, XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2, XNodeParent<? extends IVar> r3,
			XNodeParent<? extends IVar> r4) {
		this(tuple, Arrays.asList(r1, r2, r3, r4));
	}

	public SmartTuple(List<XNodeParent<? extends IVar>> restrictions) {
		this(null, restrictions);
	}

	public SmartTuple(Stream<XNodeParent<? extends IVar>> restrictions) {
		this(null, restrictions.collect(Collectors.toList()));
	}

	public SmartTuple(XNodeParent<? extends IVar> r) {
		this((int[]) null, Arrays.asList(r));
	}

	public SmartTuple(XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2) {
		this((int[]) null, Arrays.asList(r1, r2));
	}

	public SmartTuple(XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2, XNodeParent<? extends IVar> r3) {
		this((int[]) null, Arrays.asList(r1, r2, r3));
	}

	public SmartTuple(XNodeParent<? extends IVar> r1, XNodeParent<? extends IVar> r2, XNodeParent<? extends IVar> r3, XNodeParent<? extends IVar> r4) {
		this((int[]) null, Arrays.asList(r1, r2, r3, r4));
	}

	public RestrictionSimple buildRestrictionUnary(int x, TypeConditionOperatorRel op, int v) {
		return op == LT ? new Rstr1LE(x, v, true)
				: op == LE ? new Rstr1LE(x, v, false)
						: op == GT ? new Rstr1GE(x, v, true) : op == GE ? new Rstr1GE(x, v, false) : op == NE ? new Rstr1NE(x, v) : new Rstr1EQ(x, v);

	}

	/** Called to pose a restriction of the form scp[vap] <op> val */
	private SmartTuple addRestrictionUnary(Collection<RestrictionSimple> list, int x, TypeConditionOperatorRel op, int v) {
		boolean storeEqualities = true;
		if (storeEqualities && op == EQ) {
			Kit.control(prefix[x] == STAR && scp[x].dom.isPresentValue(v), () -> " " + scp[x] + " " + prefix[x] + " " + STAR + " " + v + " " + scp[x].dom);
			prefix[x] = scp[x].dom.toIdx(v); // for a constant, we directly put it in tupIdxs (no need to build a Restriction object)
			return this;
		}
		list.add(op == LT ? new Rstr1LE(x, v, true)
				: op == LE ? new Rstr1LE(x, v, false)
						: op == GT ? new Rstr1GE(x, v, true) : op == GE ? new Rstr1GE(x, v, false) : op == NE ? new Rstr1NE(x, v) : null); // null
																																			// to
		// be // change // ????
		return this;
	}

	/** Called to pose a restriction of the form scp[vap1] <op> scp[vap2] */
	private SmartTuple addRestrictionBinary(Collection<RestrictionSimple> list, int x, TypeConditionOperatorRel op, int y) {
		list.add(op == LT ? new Rstr2L(x, y, true)
				: op == LE ? new Rstr2L(x, y, false)
						: op == GE ? new Rstr2G(x, y, false)
								: op == GT ? new Rstr2G(x, y, true)
										: op == NE ? new Rstr2NE(x, y)
												: scp[0].dom.typeIdentifier() == scp[1].dom.typeIdentifier() ? new Rstr2EQ(x, y) : new Rstr2EQVal(x, y));
		return this;
	}

	/** Called to pose a restriction of the form scp[vap1] >= scp[vap2] + cst or scp[vap1] > scp[vap2] + cst */
	private SmartTuple addRestrictionBinary(Collection<RestrictionSimple> list, int x, TypeConditionOperatorRel op, int y, int cst) {
		RestrictionSimple restriction = null;
		if (op == TypeConditionOperatorRel.GE)
			restriction = new Rstr2pG(x, y, false, cst);
		else if (op == TypeConditionOperatorRel.GT)
			restriction = new Rstr2pG(x, y, true, cst);
		else
			Kit.exit("Currently, unimplemented operator " + op);
		list.add(restriction);
		return this;
	}

	public void attach(ExtensionSmart ctr) {
		this.scp = ctr.scp;
		this.prefixWithValues = prefixWithValues != null ? prefixWithValues : Kit.repeat(STAR, scp.length);
		this.prefix = IntStream.range(0, scp.length).map(i -> prefixWithValues[i] == STAR ? STAR : scp[i].dom.toIdx(prefixWithValues[i])).toArray();
		this.supportlesss = ctr.unsupported;
		this.tmp = new int[Variable.maxInitDomSize(scp)];
		assert Variable.areSortedDomainsIn(scp);

		// this code is for converting and collecting restrictions
		Collection<RestrictionSimple> list = new ArrayList<>();
		for (XNodeParent<? extends IVar> tr : collectedTreeRestrictions) {
			if (tr.sons.length == 2) {
				XNode<? extends IVar> son0 = tr.sons[0], son1 = tr.sons[1];
				Utilities.control(son0.type == TypeExpr.VAR, "Left side operand must be a variable");
				Utilities.control(son1.type != TypeExpr.SYMBOL, "Symbolic values not possible for the moment");
				Variable x = (Variable) ((XNodeLeaf<?>) son0).value;
				if (son0.type == TypeExpr.VAR && son1.type == TypeExpr.LONG) {
					int val = Utilities.safeInt(((long) ((XNodeLeaf<?>) son1).value));
					TypeConditionOperatorRel op = Types.valueOf(TypeConditionOperatorRel.class, tr.type.lcname);
					addRestrictionUnary(list, ctr.positionOf(x), op, val);
				} else if (son0.type == TypeExpr.VAR && son1.type == TypeExpr.VAR) {
					Variable y = (Variable) ((XNodeLeaf<?>) son1).value;
					TypeConditionOperatorRel op = Types.valueOf(TypeConditionOperatorRel.class, tr.type.lcname);
					addRestrictionBinary(list, ctr.positionOf(x), op, ctr.positionOf(y));
				} else if (son0.type == TypeExpr.VAR && son1.type == TypeExpr.ADD) {
					XNode<?>[] grandSons = ((XNodeParent<?>) son1).sons;
					if (grandSons.length == 2 && grandSons[0].type == TypeExpr.VAR && grandSons[1].type == TypeExpr.LONG) {
						Variable y = (Variable) ((XNodeLeaf<?>) grandSons[0]).value;
						int val = Utilities.safeInt(((long) ((XNodeLeaf<?>) grandSons[1]).value));
						TypeConditionOperatorRel op = Types.valueOf(TypeConditionOperatorRel.class, tr.type.lcname);
						addRestrictionBinary(list, ctr.positionOf(x), op, ctr.positionOf(y), val);
					} else
						Kit.exit("Currently, unimplemented case");
				} else
					Kit.exit("Currently, unimplemented case");
			}
		}
		int[] cnt1 = new int[scp.length], cnt2 = new int[scp.length]; // for each vap, number of times it is seen at left (1), and at right
																		// (2)
		list.stream().forEach(r -> cnt1[r.x]++);
		list.stream().filter(r -> r instanceof Rstr2).forEach(r -> cnt2[((Rstr2) r).y]++);

		// control coherence of restrictions
		// for (int i = 0; i < cnt1.length; i++) {
		// Kit.control(ctr.pb.rs.cp.experimental.save4Baudouin || tupIdxs[i] == STAR_INT || (cnt1[i] == 0 && cnt2[i] == 0));
		// Kit.control(ctr.pb.rs.cp.experimental.save4Baudouin || cnt2[i] <= (cnt1[i] == 0 ? 1 : 0),
		// () -> Kit.join(list, "\t") + "\t" + Kit.join(cnt1) + "\t" + Kit.join(cnt2));
		// }
		// List<Integer> listStar = new ArrayList<Integer>(), listIdx = new ArrayList<Integer>();
		// for (int i = 0; i < tupIdxs.length; i++) if (tupIdxs[i] != Table.STAR_VALUE) listIdx.add(i); else if (nb1[i] == 0 && nb2[i] == 0)
		// listStar.add(i);
		// unrestrictedIdxs = Kit.toIntArray(listIdx); unrestrictedStars = Kit.toIntArray(listStar);

		Map<Integer, List<RestrictionSimple>> byVap = list.stream().collect(Collectors.groupingBy(r -> r.x));
		restrictions = byVap.entrySet().stream().map(e -> e.getValue().size() == 1 ? e.getValue().get(0) : new RestrictionMultiple(e.getKey(), e.getValue()))
				.toArray(RestrictionSimple[]::new);

		whichRestrictions = new RestrictionSimple[scp.length];
		for (RestrictionSimple r : restrictions) {
			whichRestrictions[r.x] = r;
			if (r instanceof Rstr2)
				whichRestrictions[((Rstr2) r).y] = r;
			else if (r instanceof RestrictionMultiple)
				for (RestrictionSimple rr : ((RestrictionMultiple) r).involvedRestrictions)
					if (rr instanceof Rstr2)
						whichRestrictions[((Rstr2) rr).y] = r;
		}
	}

	/**
	 * Returns true iff the the smart tuple "contains" the specified tuple of indexes.
	 */
	public boolean contains(int[] t) {
		for (int i = 0; i < t.length; i++)
			if (prefix[i] != STAR && prefix[i] != t[i])
				return false;
		for (RestrictionSimple restriction : restrictions)
			if (!restriction.checkIndexes(t))
				return false;
		return true;
	}

	/**
	 * Returns true iff the the smart tuple is valid, considering the specified set of positions to check.
	 */
	public final boolean isValid(int[] sVal, int sValSize) {
		valTime++;
		for (int i = sValSize - 1; i >= 0; i--) {
			int x = sVal[i];
			RestrictionSimple restriction = whichRestrictions[x];
			if (restriction == null) {
				int a = prefix[x];
				if (a != STAR && !scp[x].dom.isPresent(a))
					return false;
			} else if (restriction.valTimeLocal != valTime && !restriction.isValid())
				return false;
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
			if (supportlesss[x].isEmpty()) {
				sSup[i] = sSup[--sSupSize];
				continue; // may have been emptied as vap2 when collecting on binary restrictions
			}
			RestrictionSimple restriction = whichRestrictions[x];
			if (restriction == null) {
				int a = prefix[x];
				if (a == STAR)
					supportlesss[x].clear();
				else
					supportlesss[x].remove(a);
			} else if (restriction.supTimeLocal != supTime)
				restriction.collect();
			if (supportlesss[x].isEmpty())
				sSup[i] = sSup[--sSupSize];

		}
		return sSupSize;
	}

	@Override
	public String toString() {
		String s = "Smart tuple : ";
		s += prefix == null ? "" : Kit.join(prefix, (Integer i) -> i == STAR ? "*" : i.toString());
		boolean b = true;
		if (b)
			return s + " : " + Stream.of(restrictions).map(r -> r.toString()).collect(Collectors.joining(", "));
		s += "\n  " + restrictions.length + " restrictons : ";
		for (RestrictionSimple r : restrictions)
			s += "\n    Restriction " + r.toString() + " ";
		for (int i = 0; i < whichRestrictions.length; i++)
			if (whichRestrictions[i] != null)
				s += "\n    " + scp[i] + " in restriction with vap " + whichRestrictions[i].x + " ";
		return s;
	}

	/**********************************************************************************************
	 * Root class for restrictions
	 *********************************************************************************************/

	public abstract class RestrictionAbstract {

		protected long valTimeLocal, supTimeLocal;

		/** Returns true iff the restriction is valid. */
		public abstract boolean isValid();

		/** Updates the involved set(s) of supportless indices. */
		public abstract void collect();

		/** Returns true iff the restriction validates the specified tuple of indexes. */
		public abstract boolean checkIndexes(int[] t);
	}

	/**
	 * A restriction always involves a variable whose value in the initially specified tuple is *.
	 */
	public abstract class RestrictionSimple extends RestrictionAbstract {

		/** (Position in the constraint scope of) the variable x at the right side of the restriction. */
		protected int x;

		/** The domain of x. Redundant field. */
		protected Domain domx;

		/** This set contains the indices of values in dom that have not been proved to have a support yet in the constraint. */
		protected SetSparse supportlessx;

		protected RestrictionSimple(int x) {
			this.x = x;
			this.domx = scp[x].dom;
			this.supportlessx = supportlesss[x];
			Kit.control(prefix[x] == STAR);
		}

		/**
		 * Returns true iff the specified (value) index for the variable x is valid, i.e. the restriction is valid for the smart tuple when x is set
		 * to (the value corresponding to) a.
		 */
		public abstract boolean isValidFor(int a);
	}

	/**********************************************************************************************
	 * Classes for unary restrictions of the form x <op> v
	 *********************************************************************************************/

	/**
	 * Restriction of the form x <op> v with <op> in {lt,le,ge,gt,ne,eq}. We store such a restriction by recording x (actually, its position) and
	 * pivot (for the index of the value in dom(x) that is related to v ; see subclass constructors for details). <br />
	 * The operation <op> corresponds to the chosen subclass.
	 */
	abstract class Rstr1 extends RestrictionSimple {

		/** Index of the value in the domain of x that is related to the value specified at construction (in subclasses). */
		protected int pivot;

		protected Rstr1(int x) {
			super(x);
		}

		@Override
		public String toString() {
			return scp[x] + " " + getClass().getSimpleName().substring(getClass().getSimpleName().length() - 2) + " " + scp[x].dom.toVal(pivot);
		}
	}

	final class Rstr1LE extends Rstr1 {

		protected Rstr1LE(int x, int v, boolean strict) {
			super(x);
			// we compute the greatest (value) index less than v ; both strict and non-strict cases handled with the computed pivot
			this.pivot = IntStream.range(0, domx.initSize()).map(a -> domx.initSize() - 1 - a).filter(a -> domx.toVal(a) <= v + (strict ? -1 : 0)).findFirst()
					.orElse(-1);
		}

		@Override
		public boolean isValidFor(int a) {
			return a <= pivot;
		}

		@Override
		public boolean isValid() {
			return domx.first() <= pivot;
		}

		@Override
		public void collect() {
			// three ways of collecting
			int roughNbValidValues = pivot - domx.first(), roughNbInvalidValues = domx.last() - pivot;
			if (roughNbInvalidValues < roughNbValidValues && roughNbInvalidValues < supportlessx.size()) {
				int cnt = 0;
				for (int a = domx.last(); a != -1 && a > pivot; a = domx.prev(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			} else if (roughNbValidValues < supportlessx.size()) {
				for (int a = domx.first(); a != -1 && a <= pivot; a = domx.next(a))
					supportlessx.remove(a);
			} else
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (a <= pivot)
						supportlessx.remove(a);
				}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] <= pivot;
		}
	}

	final class Rstr1GE extends Rstr1 {

		protected Rstr1GE(int x, int v, boolean strict) {
			super(x);
			// we compute the smallest (value) index greater than v ; both strict and non-strict cases handled with the computed pivot
			this.pivot = IntStream.range(0, domx.initSize()).filter(a -> domx.toVal(a) >= v + (strict ? 1 : 0)).findFirst().orElse(domx.initSize());
		}

		@Override
		public boolean isValidFor(int a) {
			return a >= pivot;
		}

		@Override
		public boolean isValid() {
			return domx.last() >= pivot;
		}

		@Override
		public void collect() {
			// three ways of collecting
			int roughNbValidValues = domx.last() - pivot, roughNbInvalidValues = pivot - domx.first();
			if (roughNbInvalidValues < roughNbValidValues && roughNbInvalidValues < supportlessx.size()) {
				int cnt = 0;
				for (int a = domx.first(); a != -1 && a < pivot; a = domx.next(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			} else if (roughNbValidValues < supportlessx.size()) {
				for (int a = domx.last(); a != -1 && a >= pivot; a = domx.prev(a))
					supportlessx.remove(a);
			} else
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (a >= pivot)
						supportlessx.remove(a);
				}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] >= pivot;
		}
	}

	final class Rstr1NE extends Rstr1 {

		protected Rstr1NE(int x, int v) {
			super(x);
			this.pivot = domx.toIdx(v);
			Kit.control(pivot != -1, () -> "useless restriction if the value does not belong to the domain");
		}

		protected Rstr1NE(int x, String v) {
			super(x);
			this.pivot = ((DomainSymbols) domx).toIdx(v);
			Kit.control(pivot != -1, () -> "useless restriction if the value does not belong to the domain");
		}

		@Override
		public boolean isValidFor(int a) {
			return a != pivot;
		}

		@Override
		public boolean isValid() {
			return domx.size() > 1 || domx.unique() != pivot;
		}

		@Override
		public void collect() {
			boolean present = supportlessx.isPresent(pivot);
			supportlessx.clear();
			if (present)
				supportlessx.add(pivot);
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] != pivot;
		}
	}

	final class Rstr1EQ extends Rstr1 {

		protected Rstr1EQ(int x, int a) {
			super(x);
			this.pivot = domx.toIdx(a);
			Kit.control(pivot != -1, () -> "inconsistent restriction if the value does not belong to the domain");
		}

		protected Rstr1EQ(int x, String v) {
			super(x);
			this.pivot = ((DomainSymbols) domx).toIdx(v);
			Kit.control(pivot != -1, () -> "inconsistent restriction if the value does not belong to the domain");
		}

		@Override
		public boolean isValidFor(int a) {
			return a == pivot;
		}

		@Override
		public boolean isValid() {
			return domx.isPresent(pivot);
		}

		@Override
		public void collect() {
			supportlessx.remove(pivot);
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] == pivot;
		}
	}

	/**********************************************************************************************
	 * Classes for binary restrictions of the form x <op> y
	 *********************************************************************************************/

	/**
	 * Restriction of the form x <op> y
	 */
	abstract class Rstr2 extends RestrictionSimple {

		/** (Position of) the second involved variable */
		protected int y;

		protected Domain domy;

		protected SetSparse supportlessy;

		protected Rstr2(int x, int y) {
			super(x);
			this.y = y;
			this.domy = scp[y].dom;
			this.supportlessy = supportlesss[y];
			Kit.control(domx.typeIdentifier() == domy.typeIdentifier() || this instanceof Rstr2EQVal);
		}

		/**
		 * Method called when the backward phase of a RestrictionStarMultiStar has been performed. More precisely, in tmp, we have exactly nb indexes
		 * for scope[vap] that are compatible with all subrestrictions of the RestrictionStarMultiStar. We call this method to perform the forward
		 * phase.
		 */
		public abstract void collectForVap2(int nb);

		@Override
		public String toString() {
			return scp[x] + " " + getClass().getSimpleName().substring(getClass().getSimpleName().length() - 2) + " " + scp[y];
		}
	}

	/** Restriction of the form scp[vap] < scp[vap2] or the form scp[vap] <= scp[vap2] */
	final class Rstr2L extends Rstr2 {
		private boolean strict;

		protected Rstr2L(int x, int y, boolean strict) {
			super(x, y);
			this.strict = strict;
		}

		@Override
		public boolean isValidFor(int a) {
			return strict ? a < domy.last() : a <= domy.last();
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			return strict ? domx.first() < domy.last() : domx.first() <= domy.last();
		}

		private void collectThroughInvalidValues() {
			int first1 = domx.first(), last2 = domy.last();
			if (!scp[x].isAssigned()) {
				int cnt = 0;
				for (int a = domx.last(); a != -1 && (strict ? a >= last2 : a > last2); a = domx.prev(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			}
			if (!scp[y].isAssigned()) {
				int cnt = 0;
				for (int a = domy.first(); a != -1 && (strict ? first1 >= a : first1 > a); a = domy.next(a))
					if (supportlessy.isPresent(a))
						tmp[cnt++] = a;
				supportlessy.resetTo(tmp, cnt);
			}
		}

		private void collectThroughSupportlessSets() {
			int first1 = domx.first(), last2 = domy.last();
			if (!scp[x].isAssigned())
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (strict ? a < last2 : a <= last2)
						supportlessx.remove(a);
				}
			if (!scp[y].isAssigned())
				for (int i = supportlessy.limit; i >= 0; i--) {
					int a = supportlessy.dense[i];
					if (strict ? first1 < a : first1 <= a)
						supportlessy.remove(a);
				}
		}

		private void collectThroughValidValues() {
			int first1 = domx.first(), last2 = domy.last();
			if (!scp[x].isAssigned())
				for (int a = domx.first(); a != -1 && (strict ? a < last2 : a <= last2); a = domx.next(a))
					supportlessx.remove(a);
			if (!scp[y].isAssigned())
				for (int a = domy.last(); a != -1 && (strict ? first1 < a : first1 <= a); a = domy.prev(a))
					supportlessy.remove(a);
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			// three parameters for choosing the cheapest way of collecting
			int roughNbInvalidValues = Math.max(domx.first() - domy.first(), 0) + Math.max(domx.last() - domy.last(), 0);
			int nSupportlessValues = supportlessx.size() + supportlessy.size();
			int roughNbValidValues = Math.min(domx.last(), domy.last()) - domx.first() + domy.last() - Math.max(domx.first(), domy.first());
			if (roughNbInvalidValues < nSupportlessValues && roughNbInvalidValues < roughNbValidValues)
				collectThroughInvalidValues();
			else if (nSupportlessValues < roughNbValidValues)
				collectThroughSupportlessSets();
			else
				collectThroughValidValues();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned()) {
				int first1 = tmp[0];
				for (int a = domy.last(); a != -1 && (strict ? first1 < a : first1 <= a); a = domy.prev(a))
					supportlessy.remove(a);
			}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return strict ? t[x] < t[y] : t[x] <= t[y];
		}

		@Override
		public String toString() {
			return scp[x] + " " + getClass().getSimpleName().charAt(getClass().getSimpleName().length() - 1) + (strict ? "T" : "E") + " " + scp[y];
		}
	}

	/** Restriction of the form x >y or the form x >= y */
	final class Rstr2G extends Rstr2 {
		private boolean strict;

		protected Rstr2G(int x, int y, boolean strict) {
			super(x, y);
			this.strict = strict;
		}

		@Override
		public boolean isValidFor(int a) {
			return strict ? a > domy.first() : a >= domy.first();
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			return strict ? domx.last() > domy.first() : domx.last() >= domy.first();
		}

		private void collectThroughInvalidValues() {
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned()) {
				int cnt = 0;
				for (int a = domx.first(); a != -1 && (strict ? a <= first2 : a < first2); a = domx.next(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			}
			if (!scp[y].isAssigned()) {
				int cnt = 0;
				for (int a = domy.last(); a != -1 && (strict ? a >= last1 : a > last1); a = domy.prev(a))
					if (supportlessy.isPresent(a))
						tmp[cnt++] = a;
				supportlessy.resetTo(tmp, cnt);
			}
		}

		private void collectThroughSupportlessSets() {
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned())
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (strict ? a > first2 : a >= first2)
						supportlessx.remove(a);
				}
			if (!scp[y].isAssigned())
				for (int i = supportlessy.limit; i >= 0; i--) {
					int a = supportlessy.dense[i];
					if (strict ? last1 > a : last1 >= a)
						supportlessy.remove(a);
				}
		}

		private void collectThroughValidValues() {
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned())
				for (int a = domx.last(); a != -1 && (strict ? a > first2 : a >= first2); a = domx.prev(a))
					supportlessx.remove(a);
			if (!scp[y].isAssigned())
				for (int a = domy.first(); a != -1 && (strict ? last1 > a : last1 >= a); a = domy.next(a))
					supportlessy.remove(a);
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			// three parameters for choosing the cheapest way of collecting
			int roughNbInvalidValues = Math.max(domy.first() - domx.first(), 0) + Math.max(domy.last() - domx.last(), 0);
			int nbSupportlessValues = supportlessx.size() + supportlessy.size();
			int roughNbValidValues = Math.min(domx.last(), domy.last()) - domy.first() + domx.last() - Math.max(domx.first(), domy.first());
			if (roughNbInvalidValues < nbSupportlessValues && roughNbInvalidValues < roughNbValidValues)
				collectThroughInvalidValues();
			else if (nbSupportlessValues < roughNbValidValues)
				collectThroughSupportlessSets();
			else
				collectThroughValidValues();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned()) {
				int last1 = tmp[nb - 1];
				for (int a = domy.first(); a != -1 && (strict ? last1 > a : last1 >= a); a = domy.next(a))
					supportlessy.remove(a);
			}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return strict ? t[x] > t[y] : t[x] >= t[y];
		}

		@Override
		public String toString() {
			return scp[x] + " " + getClass().getSimpleName().charAt(getClass().getSimpleName().length() - 1) + (strict ? "T" : "E") + " " + scp[y];
		}
	}

	final class Rstr2NE extends Rstr2 {

		protected Rstr2NE(int x, int y) {
			super(x, y);
		}

		@Override
		public boolean isValidFor(int a) {
			return domy.size() > 1 || a != domy.unique();
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			return domx.size() > 1 || domy.size() > 1 || domx.unique() != domy.unique();
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			if (!scp[x].isAssigned())
				if (domy.size() == 1 && supportlessx.isPresent(domy.unique()))
					supportlessx.resetTo(domy.unique());
				else
					supportlessx.clear();
			if (!scp[y].isAssigned())
				if (domx.size() == 1 && supportlessy.isPresent(domx.unique()))
					supportlessy.resetTo(domx.unique());
				else
					supportlessy.clear();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned())
				if (nb == 1 && supportlessy.isPresent(tmp[0]))
					supportlessy.resetTo(tmp[0]);
				else
					supportlessy.clear();
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] != t[y];
		}
	}

	final class Rstr2EQ extends Rstr2 {
		private int residue;
		private boolean newResidue;

		protected Rstr2EQ(int x, int y) {
			super(x, y);
		}

		@Override
		public boolean isValidFor(int a) {
			return domy.isPresent(a);
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			newResidue = false;
			if (domx.isPresent(residue) && domy.isPresent(residue))
				return true;
			newResidue = true;
			Domain domSmall = domx.size() < domy.size() ? domx : domy;
			Domain domBig = domSmall == domx ? domy : domx;
			for (int a = domSmall.first(); a != -1; a = domSmall.next(a))
				if (domBig.isPresent(a)) {
					residue = a;
					return true;
				}
			return false;
		}

		private void collectThroughRemovedValues() {
			if (!scp[x].isAssigned()) {
				int cnt = 0;
				for (int a = domy.lastRemoved(); a != -1; a = domy.prevRemoved(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			}
			if (!scp[y].isAssigned()) {
				int cnt = 0;
				for (int a = domx.lastRemoved(); a != -1; a = domx.prevRemoved(a))
					if (supportlessy.isPresent(a))
						tmp[cnt++] = a;
				supportlessy.resetTo(tmp, cnt);
			}
		}

		private void collectThroughSmallestDomain() {
			// if (scp[0].problem.solver.getDepth() == 231)
			// Kit.prn("collectSmall " + newResidue + " " + idxResidue);
			Domain domSmall = domx.size() < domy.size() ? domx : domy;
			Domain domBig = domSmall == domx ? domy : domx;
			if (!scp[x].isAssigned() && !scp[y].isAssigned()) {
				for (int a = valTimeLocal == valTime && newResidue ? residue : domSmall.first(); a != -1; a = domSmall.next(a))
					if (domBig.isPresent(a)) {
						supportlessx.remove(a);
						supportlessy.remove(a);
					}
			} else if (!scp[x].isAssigned()) {
				for (int a = valTimeLocal == valTime && newResidue ? residue : domSmall.first(); a != -1; a = domSmall.next(a))
					if (domBig.isPresent(a))
						supportlessx.remove(a);
			} else if (!scp[y].isAssigned()) {
				for (int a = valTimeLocal == valTime && newResidue ? residue : domSmall.first(); a != -1; a = domSmall.next(a))
					if (domBig.isPresent(a))
						supportlessy.remove(a);
			}
		}

		private void collectThroughSupportlessSets() {
			if (!scp[x].isAssigned())
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (domy.isPresent(a))
						supportlessx.remove(a);
				}
			if (!scp[y].isAssigned())
				for (int i = supportlessy.limit; i >= 0; i--) {
					int a = supportlessy.dense[i];
					if (domx.isPresent(a))
						supportlessy.remove(a);
				}
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			// three parameters for choosing the cheapest way of collecting
			int nbRemovedValues = domx.nRemoved() + domy.nRemoved();
			int nbSupportlessValues = supportlessx.size() + supportlessy.size();
			int minDomainSize = Math.min(domx.size(), domy.size());
			if (nbRemovedValues < nbSupportlessValues && nbRemovedValues < minDomainSize)
				collectThroughRemovedValues();
			else if (nbSupportlessValues < minDomainSize)
				collectThroughSupportlessSets();
			else
				collectThroughSmallestDomain();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned())
				for (int i = 0; i < nb; i++)
					supportlessy.remove(tmp[i]);
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return t[x] == t[y];
		}
	}

	final class Rstr2EQVal extends Rstr2 {
		private int valResidue;
		boolean newResidue;

		protected Rstr2EQVal(int x, int y) {
			super(x, y);
		}

		@Override
		public boolean isValidFor(int a) {
			return domy.toPresentIdx(domx.toVal(a)) != -1;
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			newResidue = false;
			if (domx.toPresentIdx(valResidue) != -1 && domy.toPresentIdx(valResidue) != -1)
				return true;
			newResidue = true;
			Domain domSmall = domx.size() < domy.size() ? domx : domy;
			Domain domBig = domSmall == domx ? domy : domx;
			for (int a = domSmall.first(); a != -1; a = domSmall.next(a)) {
				int v = domSmall.toVal(a);
				if (domBig.toPresentIdx(v) != -1) {
					valResidue = v;
					return true;
				}
			}
			return false;
		}

		private void collectThroughRemovedValues() {
			if (!scp[x].isAssigned()) {
				int cnt = 0;
				for (int a = domy.lastRemoved(); a != -1; a = domy.prevRemoved(a)) {
					int v = domy.toVal(a);
					int b = domx.toPresentIdx(v);
					if (b != -1 && supportlessx.isPresent(b))
						tmp[cnt++] = b;
				}
				supportlessx.resetTo(tmp, cnt);
			}
			if (!scp[y].isAssigned()) {
				int cnt = 0;
				for (int a = domx.lastRemoved(); a != -1; a = domx.prevRemoved(a)) {
					// System.out.println("Idx=" + idx + " " + dom.prevDelIdx(idx));
					int v = domx.toVal(a);
					int b = domy.toPresentIdx(v);
					if (b != -1 && supportlessy.isPresent(b)) {
						// System.out.println(idx + " " + tmp.length + " " + dom.size() + " " + dom.initSize() + " cnt=" + cnt);
						tmp[cnt++] = b;

					}
				}
				supportlessy.resetTo(tmp, cnt);
			}
		}

		private void collectThroughSmallestDomain() {
			Domain domSmall = domx.size() < domy.size() ? domx : domy;
			Domain domBig = domSmall == domx ? domy : domx;
			if (!scp[x].isAssigned() && !scp[y].isAssigned()) {
				for (int a = domSmall.first(); a != -1; a = domSmall.next(a)) {
					int v = domSmall.toVal(a);
					int b = domBig.toPresentIdx(v);
					if (b != -1) {
						supportlessx.remove(domSmall == domx ? a : b);
						supportlessy.remove(domSmall == domx ? b : a);
					}
				}
			} else if (!scp[x].isAssigned()) {
				for (int a = domSmall.first(); a != -1; a = domSmall.next(a)) {
					int v = domSmall.toVal(a);
					int b = domBig.toPresentIdx(v);
					if (b != -1)
						supportlessx.remove(domSmall == domx ? a : b);
				}
			} else if (!scp[y].isAssigned()) {
				for (int a = domSmall.first(); a != -1; a = domSmall.next(a)) {
					int v = domSmall.toVal(a);
					int b = domBig.toPresentIdx(v);
					if (b != -1)
						supportlessy.remove(domSmall == domx ? b : a);
				}
			}
		}

		private void collectThroughSupportlessSets() {
			if (!scp[x].isAssigned())
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					int v = domx.toVal(a);
					int b = domy.toPresentIdx(v);
					if (b != -1)
						supportlessx.remove(a);
				}
			if (!scp[y].isAssigned())
				for (int i = supportlessy.limit; i >= 0; i--) {
					int a = supportlessy.dense[i];
					int v = domy.toVal(a);
					int b = domx.toPresentIdx(v);
					if (b != -1)
						supportlessy.remove(a);
				}
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			// three parameters for choosing the cheapest way of collecting
			int nbRemovedValues = domx.nRemoved() + domy.nRemoved();
			int nbSupportlessValues = supportlessx.size() + supportlessy.size();
			int minDomainSize = Math.min(domx.size(), domy.size());
			if (nbRemovedValues < nbSupportlessValues && nbRemovedValues < minDomainSize)
				collectThroughRemovedValues();
			else if (nbSupportlessValues < minDomainSize)
				collectThroughSupportlessSets();
			else
				collectThroughSmallestDomain();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned())
				for (int i = 0; i < nb; i++) {
					int a = tmp[i];
					int v = domx.toVal(a);
					int b = domy.toPresentIdx(v);
					if (b != -1) // && supportless2.isPresent(idxx))
						supportlessy.remove(b);
				}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return domx.toVal(t[x]) == domy.toVal(t[y]);
		}
	}

	/**
	 * Restriction of the form x > y + cst or the form x >= y + cst
	 */
	final class Rstr2pG extends Rstr2 {
		private boolean strict;
		private int cst;

		protected Rstr2pG(int x, int y, boolean strict, int cst) {
			super(x, y);
			this.strict = strict;
			this.cst = cst;
			Kit.control(scp[x].dom instanceof DomainRange && scp[y].dom instanceof DomainRange);
		}

		@Override
		public boolean isValidFor(int a) {
			return strict ? a > domy.first() + cst : a >= domy.first() + cst;
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			return strict ? domx.last() > domy.first() + cst : domx.last() >= domy.first() + cst;
		}

		private void collectThroughInvalidValues() {
			// Kit.prn("here1");
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned()) {
				int cnt = 0;
				for (int a = domx.first(); a != -1 && (strict ? a <= first2 + cst : a < first2 + cst); a = domx.next(a))
					if (supportlessx.isPresent(a))
						tmp[cnt++] = a;
				supportlessx.resetTo(tmp, cnt);
			}
			if (!scp[y].isAssigned()) {
				int cnt = 0;
				for (int a = domy.last(); a != -1 && (strict ? a + cst >= last1 : a + cst > last1); a = domy.prev(a))
					if (supportlessy.isPresent(a))
						tmp[cnt++] = a;
				supportlessy.resetTo(tmp, cnt);
			}
		}

		private void collectThroughSupportlessSets() {
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned())
				for (int i = supportlessx.limit; i >= 0; i--) {
					int a = supportlessx.dense[i];
					if (strict ? a > first2 + cst : a >= first2 + cst)
						supportlessx.remove(a);
				}
			if (!scp[y].isAssigned())
				for (int i = supportlessy.limit; i >= 0; i--) {
					int a = supportlessy.dense[i];
					if (strict ? last1 > a + cst : last1 >= a + cst)
						supportlessy.remove(a);
				}
		}

		private void collectThroughValidValues() {
			// Kit.prn("here3");
			int last1 = domx.last(), first2 = domy.first();
			if (!scp[x].isAssigned())
				for (int a = domx.last(); a != -1 && (strict ? a > first2 + cst : a >= first2 + cst); a = domx.prev(a))
					supportlessx.remove(a);
			if (!scp[y].isAssigned())
				for (int a = domy.first(); a != -1 && (strict ? last1 > a + cst : last1 >= a + cst); a = domy.next(a))
					supportlessy.remove(a);
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			// three parameters for choosing the cheapest way of collecting
			int roughNbInvalidValues = Math.max(domy.first() + cst - domx.first(), 0) + Math.max(domy.last() + cst - domx.last(), 0);
			int nbSupportlessValues = supportlessx.size() + supportlessy.size();
			int roughNbValidValues = Math.min(domx.last(), domy.last()) + cst - domy.first() + domx.last() - Math.max(domx.first(), domy.first() + cst);
			if (roughNbInvalidValues < nbSupportlessValues && roughNbInvalidValues < roughNbValidValues)
				collectThroughInvalidValues();
			else if (nbSupportlessValues < roughNbValidValues)
				collectThroughSupportlessSets();
			else
				collectThroughValidValues();
		}

		@Override
		public void collectForVap2(int nb) {
			if (!scp[y].isAssigned()) {
				int last1 = tmp[nb - 1];
				for (int a = domy.first(); a != -1 && (strict ? last1 > a + cst : last1 >= a + cst); a = domy.next(a))
					supportlessy.remove(a);
			}
		}

		@Override
		public boolean checkIndexes(int[] t) {
			return strict ? t[x] > t[y] + cst : t[x] >= t[y] + cst;
		}

		@Override
		public String toString() {
			return scp[x] + " " + getClass().getSimpleName().charAt(getClass().getSimpleName().length() - 1) + (strict ? "T" : "E") + " " + scp[y] + " + "
					+ cst;
		}
	}

	/**********************************************************************************************
	 * Classes for restrictions of the form x <op1> y and x <op2> z ...
	 *********************************************************************************************/

	/**
	 * Restriction of the form x <op1> y and x <op2> z ...
	 */
	final class RestrictionMultiple extends RestrictionSimple {
		/**
		 * The restrictions involved in this multiple restriction. All involved restrictions are on the same variable
		 */
		protected RestrictionSimple[] involvedRestrictions;

		protected int cnt;

		protected RestrictionMultiple(int x, List<RestrictionSimple> restrictions) {
			super(x);
			this.involvedRestrictions = restrictions.toArray(new RestrictionSimple[restrictions.size()]);
			assert Stream.of(involvedRestrictions).allMatch(r -> r.x == x);
		}

		@Override
		public boolean isValidFor(int a) {
			for (RestrictionSimple restriction : involvedRestrictions)
				if (!restriction.isValidFor(a))
					return false;
			return true;
		}

		@Override
		public boolean isValid() {
			valTimeLocal = valTime;
			// we collect in tmp the valid (value) indexes for x
			cnt = 0;
			for (int a = domx.first(); a != -1; a = domx.next(a))
				if (isValidFor(a))
					tmp[cnt++] = a;
			return cnt > 0;
		}

		@Override
		public void collect() {
			supTimeLocal = supTime;
			if (valTimeLocal != valTime) {
				boolean valid = isValid();
				assert valid;
			}
			// we update the set of supportless idxs for vap
			if (!scp[x].isAssigned())
				for (int i = 0; i < cnt; i++)
					supportlessx.remove(tmp[i]);
			// we update the set of supportless idxs for the other involved stars
			for (RestrictionSimple restriction : involvedRestrictions)
				if (restriction instanceof Rstr2)
					((Rstr2) restriction).collectForVap2(cnt);
		}

		@Override
		public boolean checkIndexes(int[] t) {
			for (RestrictionSimple restriction : involvedRestrictions)
				if (!restriction.checkIndexes(t))
					return false;
			return true;
		}

		@Override
		public String toString() {
			return Stream.of(involvedRestrictions).map(r -> r.toString()).collect(Collectors.joining(", "));
			// return "Multiple restrictions: " + Stream.of(involvedRestrictions).map(r -> r.toString()).collect(Collectors.joining("\n"));
		}
	}

	/**
	 * restriction of the form *i <op> *j + k <br />
	 * TODO to be implemented later
	 */
	abstract class RestrictionStarStarConstant extends Rstr2 {

		protected int cst;

		protected RestrictionStarStarConstant(int x, int y, int cst) {
			super(x, y);
			this.cst = cst;
		}
	}
}
