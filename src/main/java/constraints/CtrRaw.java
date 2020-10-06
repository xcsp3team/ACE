/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.Utilities;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

import problem.Problem;
import variables.Variable;

public class CtrRaw extends Constraint {
	private Map<String, Object> map;

	@Override
	public Map<String, Object> mapXCSP() {
		return map;
	}

	public CtrRaw(Problem pb, IVar[] scp, Map<String, Object> map) {
		super(pb, Stream.of(scp).map(x -> (Variable) x).toArray(Variable[]::new));
		this.map = map;
	}

	public static class RawIntension extends CtrRaw implements ICtrIntension {

		public RawIntension(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawIntension buildFrom(Problem pb, IVar[] scp, XNodeParent<IVar> _tree) {
			return new RawIntension(pb, scp, map(SCOPE, scp, FUNCTION, _tree));
		}
	}

	public static class RawExtension extends CtrRaw implements ICtrExtension {

		public RawExtension(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawExtension buildFrom(Problem pb, IVar[] scp, String _list, int _arity, int[][] _tuples, boolean _positive) {
			return new RawExtension(pb, scp, map(SCOPE, scp, LIST, _list, ARITY, _arity, TUPLES, _tuples, POSITIVE, _positive));
		}

		public static RawExtension buildFrom(Problem pb, IVar[] scp, String _list, int _arity, String[][] _tuples, boolean _positive) {
			return new RawExtension(pb, scp, map(SCOPE, scp, LIST, _list, ARITY, _arity, TUPLES, _tuples, POSITIVE, _positive));
		}
	}

	public static class RawRegular extends CtrRaw implements ICtrRegular {

		public RawRegular(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawRegular buildFrom(Problem pb, IVar[] scp, String _list, String _transitions, String _startState, String[] _finalStates) {
			return new RawRegular(pb, scp, map(SCOPE, scp, LIST, _list, TRANSITIONS, _transitions, START, _startState, FINAL, Utilities.join(_finalStates)));
		}
	}

	public static class RawMdd extends CtrRaw implements ICtrMdd {

		public RawMdd(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawMdd buildFrom(Problem pb, IVar[] scp, String _list, String _transitions) {
			return new RawMdd(pb, scp, map(SCOPE, scp, LIST, _list, TRANSITIONS, _transitions));
		}
	}

	public static class RawAllDifferent extends CtrRaw implements ICtrAllDifferent {

		public RawAllDifferent(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawAllDifferent buildFrom(Problem pb, IVar[] scp, String _key1, Object _value1, String _except) {
			Utilities.control(_except == null || _except.length() > 0, "Pb with except values");
			return new RawAllDifferent(pb, scp, map(SCOPE, scp, _key1, _value1, EXCEPT, _except));
		}
	}

	// allDifferent matruix
	// @Override
	// public boolean checkVals(int[] t) {
	// int n = matrix.length, m = matrix[0].length;
	// for (int i = 0; i < n; i++)
	// for (int j = 0; j < m; j++)
	// for (int k = j + 1; k < m; k++)
	// if (t[i * m + j] == t[i * m + k])
	// return false;
	// for (int i = 0; i < n; i++)
	// for (int j = 0; j < m; j++)
	// for (int k = j + 1; k < m; k++)
	// if (t[j * m + i] == t[k * m + i])
	// return false;
	// return true;
	// }

	public static class RawAllEqual extends CtrRaw implements ICtrAllEqual {

		public RawAllEqual(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawAllEqual buildFrom(Problem pb, IVar[] scp, final String _key, Object _value) {
			return new RawAllEqual(pb, scp, map(SCOPE, scp, _key, _value));
		}
	}

	public static class RawOrdered extends CtrRaw implements ICtrOrdered {

		public RawOrdered(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawOrdered buildFrom(Problem pb, IVar[] scp, String _list, String _lengths, TypeOperatorRel _operator) {
			return new RawOrdered(pb, scp, map(SCOPE, scp, LIST, _list, LENGTHS, _lengths, OPERATOR, _operator.name().toLowerCase()));
		}

		public static RawOrdered buildFrom(Problem pb, IVar[] scp, String _key1, Object _value1, TypeOperatorRel _operator) {
			return new RawOrdered(pb, scp, map(SCOPE, scp, _key1, _value1, OPERATOR, _operator.name().toLowerCase()));
		}
	}

	public static class RawSum extends CtrRaw implements ICtrSum {

		public RawSum(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawSum buildFrom(Problem pb, IVar[] scp, String _list, Object _coeffs, Condition _condition) {
			return new RawSum(pb, scp, map(SCOPE, scp, LIST, _list, COEFFS, _coeffs, CONDITION, _condition));
		}
	}

	public static class RawCount extends CtrRaw implements ICtrCount {

		public RawCount(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawCount buildFrom(Problem pb, IVar[] scp, String _list, Object _values, Condition _condition) {
			return new RawCount(pb, scp, map(SCOPE, scp, LIST, _list, VALUES, _values, CONDITION, _condition));
		}
	}

	public static class RawNValues extends CtrRaw implements ICtrNValues {

		public RawNValues(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawNValues buildFrom(Problem pb, IVar[] scp, String _list, Object _except, Condition _condition) {
			return new RawNValues(pb, scp, map(SCOPE, scp, LIST, _list, EXCEPT, _except, CONDITION, _condition));
		}
	}

	public static class RawCardinality extends CtrRaw implements ICtrCardinality {

		public RawCardinality(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawCardinality buildFrom(Problem pb, IVar[] scp, String _list, String _values, Boolean _closed, String _occurs) {
			return new RawCardinality(pb, scp, map(SCOPE, scp, LIST, _list, VALUES, _values, CLOSED, _closed, OCCURS, _occurs));
		}
	}

	public static class RawExtremum {
		public static CtrRaw buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, Object _index, TypeRank _rank, Condition _condition,
				boolean minimum) {
			if (minimum)
				return RawMinimum.buildFrom(pb, scp, _list, _startIndex, _index, _rank, _condition);
			return RawMaximum.buildFrom(pb, scp, _list, _startIndex, _index, _rank, _condition);
		}
	}

	public static class RawMaximum extends CtrRaw implements ICtrMaximum {

		public RawMaximum(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawMaximum buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, Object _index, TypeRank _rank, Condition _condition) {
			return new RawMaximum(pb, scp, map(SCOPE, scp, LIST, _list, START_INDEX, _startIndex, INDEX, _index, RANK, _rank, CONDITION, _condition));
		}
	}

	public static class RawMinimum extends CtrRaw implements ICtrMinimum {

		public RawMinimum(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawMinimum buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, Object _index, TypeRank _rank, Condition _condition) {
			return new RawMinimum(pb, scp, map(SCOPE, scp, LIST, _list, START_INDEX, _startIndex, INDEX, _index, RANK, _rank, CONDITION, _condition));
		}
	}

	public static class RawElement extends CtrRaw implements ICtrElement {

		public RawElement(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawElement buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, Object _index, TypeRank _rank, Object _value) {
			return new RawElement(pb, scp, map(SCOPE, scp, LIST, _list, START_INDEX, _startIndex, INDEX, _index, RANK, _rank, VALUE, _value));
		}
	}

	public static class RawChannel extends CtrRaw implements ICtrChannel {

		public RawChannel(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawChannel buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, String _list2, Integer _startIndex2, Object _value) {
			return new RawChannel(pb, scp, map(SCOPE, scp, LIST, _list, START_INDEX, _startIndex, LIST2, _list2, START_INDEX2, _startIndex2, VALUE, _value));
		}
	}

	public static class RawStretch extends CtrRaw implements ICtrStretch {

		public RawStretch(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawStretch buildFrom(Problem pb, IVar[] scp, String _list, String _values, String _widths, String _patterns) {
			return new RawStretch(pb, scp, map(SCOPE, scp, LIST, _list, VALUES, _values, WIDTHS, _widths, PATTERNS, _patterns));
		}
	}

	public static class RawNoOverlap extends CtrRaw implements ICtrNoOverlap {

		public RawNoOverlap(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawNoOverlap buildFrom(Problem pb, IVar[] scp, String _origins, String _lengths, Boolean _zeroIgnored) {
			return new RawNoOverlap(pb, scp, map(SCOPE, scp, ORIGINS, _origins, LENGTHS, _lengths, ZERO_IGNORED, _zeroIgnored));
		}
	}

	public static class RawCumulative extends CtrRaw implements ICtrCumulative {

		public RawCumulative(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawCumulative buildFrom(Problem pb, IVar[] scp, String _origins, String _lengths, String _ends, String _heights, Condition _condition) {
			return new RawCumulative(pb, scp, map(SCOPE, scp, ORIGINS, _origins, LENGTHS, _lengths, ENDS, _ends, HEIGHTS, _heights, CONDITION, _condition));
		}
	}

	public static class RawCircuit extends CtrRaw implements ICtrCircuit {

		public RawCircuit(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawCircuit buildFrom(Problem pb, IVar[] scp, String _list, Integer _startIndex, Object _size) {
			return new RawCircuit(pb, scp, map(SCOPE, scp, LIST, _list, START_INDEX, _startIndex, SIZE, _size));
		}
	}

	public static class RawClause extends CtrRaw implements ICtrClause {

		public RawClause(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawClause buildFrom(Problem pb, IVar[] scp, String _list) {
			return new RawClause(pb, scp, map(SCOPE, scp, LIST, _list));
		}
	}

	public static class RawInstantiation extends CtrRaw implements ICtrInstantiation {

		public RawInstantiation(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawInstantiation buildFrom(Problem pb, IVar[] scp, String _list, String _values) {
			return new RawInstantiation(pb, scp, map(SCOPE, scp, LIST, _list, VALUES, _values));
		}
	}

	public static class RawSmart extends CtrRaw implements ICtrSmart {

		public RawSmart(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawSmart buildFrom(Problem pb, IVar[] scp, String _list, String[] _rows) {
			return new RawSmart(pb, scp, map(SCOPE, scp, LIST, _list, ROWS, _rows));
		}
	}

	// ************************************************************************
	// ***** Meta-constraints
	// ************************************************************************

	public static class RawSlide extends CtrRaw implements ICtrSlide, Meta {

		public RawSlide(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawSlide buildFrom(Problem pb, IVar[] scp, Boolean _circular, IVar[][] _lists, int[] _offsets, int[] _collects, CtrAlone[] _cas) {
			return new RawSlide(pb, scp, map(SCOPE, scp, CIRCULAR, _circular, LISTS, _lists, OFFSETS, _offsets, COLLECTS, _collects, ALONES, _cas));
		}
	}

	public static class RawIfThen extends CtrRaw implements ICtrIfThen, Meta {

		public RawIfThen(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawIfThen buildFrom(Problem pb, IVar[] scp, CtrAlone _ca1, CtrAlone _ca2) {
			return new RawIfThen(pb, scp, map(SCOPE, scp, ALONES, new CtrAlone[] { _ca1, _ca2 }));
		}
	}

	public static class RawIfThenElse extends CtrRaw implements ICtrIfThenElse, Meta {

		public RawIfThenElse(Problem pb, IVar[] scp, Map<String, Object> map) {
			super(pb, scp, map);
		}

		public static RawIfThenElse buildFrom(Problem pb, IVar[] scp, CtrAlone _ca1, CtrAlone _ca2, CtrAlone _ca3) {
			return new RawIfThenElse(pb, scp, map(SCOPE, scp, ALONES, new CtrAlone[] { _ca1, _ca2, _ca3 }));
		}
	}

	// public IfThen(Problem pb, CtrHard c1, CtrHard c2) {
	// super(pb, pb.ui.distinct(pb.ui.vars(c1.scp, c2.scp)));
	// pos1 = Stream.of(c1.scp).mapToInt(x -> positionOf(x)).toArray();
	// pos2 = Stream.of(c2.scp).mapToInt(x -> positionOf(x)).toArray();
	// this.c1 = c1;
	// this.c2 = c2;
	// ca1 = pb.ctrEntities.ctrToCtrAlone.get(c1);
	// ca2 = pb.ctrEntities.ctrToCtrAlone.get(c2);
	// pb.removeCtr(c1); // we remove them since a slide is posted (useful for saving into XCSP3)
	// pb.removeCtr(c2);
	// }
	//
	// @Override
	// public boolean checkVals(int[] t) {
	// int[] t1 = IntStream.of(pos1).map(v -> t[v]).toArray();
	// int[] t2 = IntStream.of(pos2).map(v -> t[v]).toArray();
	// return !c1.checkVals(t1) || c2.checkVals(t2);
	// }

	@Override
	public void buildSupporter() {
		// TODO Auto-generated method stub

	}

	@Override
	public long costOfIdxs(int[] idxs) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public long minCostOfTuplesWith(int x, int a) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean filterFrom(Variable evt) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isSubstitutableBy(Variable x, int a, int b) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean controlArcConsistency() {
		// TODO Auto-generated method stub
		return false;
	}

}
