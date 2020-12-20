package xcsp3;

import static org.xcsp.common.Utilities.join;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_BINARY_PRIMITIVES;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_EXTREMUM_CASES;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_LOGIC_CASES;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_SUM_CASES;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_TERNARY_PRIMITIVES;
import static org.xcsp.parser.callbacks.XCallbacks.XCallbacksParameters.RECOGNIZE_UNARY_PRIMITIVES;

import java.io.File;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.Condition.ConditionVal;
import org.xcsp.common.Condition.ConditionVar;
import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeCtr;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Types.TypeFlag;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.Types.TypeVar;
import org.xcsp.common.Utilities;
import org.xcsp.common.domains.Domains.Dom;
import org.xcsp.common.domains.Domains.DomSymbolic;
import org.xcsp.common.predicates.MatcherInterface;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.common.structures.AbstractTuple;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrArray;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;
import org.xcsp.modeler.entities.ModelingEntity;
import org.xcsp.parser.XParser;
import org.xcsp.parser.callbacks.XCallbacks2;
import org.xcsp.parser.entries.ParsingEntry;
import org.xcsp.parser.entries.ParsingEntry.CEntry;
import org.xcsp.parser.entries.XConstraints.XBlock;
import org.xcsp.parser.entries.XConstraints.XCtr;
import org.xcsp.parser.entries.XConstraints.XGroup;
import org.xcsp.parser.entries.XConstraints.XLogic;
import org.xcsp.parser.entries.XConstraints.XSlide;
import org.xcsp.parser.entries.XObjectives.XObj;
import org.xcsp.parser.entries.XVariables.XArray;
import org.xcsp.parser.entries.XVariables.XVar;
import org.xcsp.parser.entries.XVariables.XVarInteger;
import org.xcsp.parser.entries.XVariables.XVarSymbolic;

import constraints.Constraint.CtrHardFalse;
import constraints.global.BinPackingSimple;
import dashboard.Arguments;
import dashboard.Control.SettingXml;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;;

/**
 * This class corresponds to a problem loading instances in XCSP3 format.
 */
public class XCSP3 implements ProblemAPI, XCallbacks2 {

	private Implem implem = new Implem(this);

	@Override
	public Implem implem() {
		return implem;
	}

	private List<String> filenames;

	@Override
	public String name() {
		return filenames.get(imp().head.instanceNumber);
	}

	private List<String> collect(List<String> list, File f) {
		if (f.isDirectory())
			Stream.of(f.listFiles()).forEach(g -> collect(list, g));
		else if (Stream.of(".xml", ".lzma").anyMatch(suf -> f.getName().endsWith(suf)))
			list.add(f.getAbsolutePath());
		return list;
	}

	public void data() { // called automatically by reflection
		this.pb = imp();
		String s = imp().askString("File or directory:");
		if (filenames == null) {
			filenames = collect(new ArrayList<>(), new File(s)).stream().sorted().collect(Collectors.toList());
			Arguments.nInstancesToSolve = filenames.size();
		}
		imp().parameters.get(0).setValue(name());
		System.out.println();
	}

	@Override
	public void model() {
		SettingXml settings = imp().head.control.xml;
		// if (settings.primitiveUnaryInSolver)
		implem().currParameters.remove(RECOGNIZE_UNARY_PRIMITIVES);
		// if (settings.primitiveBinaryInSolver)
		implem().currParameters.remove(RECOGNIZE_BINARY_PRIMITIVES);
		// if (settings.primitiveTernaryInSolver)
		implem().currParameters.remove(RECOGNIZE_TERNARY_PRIMITIVES);
		// if (settings.recognizeLogicInSolver)
		implem().currParameters.remove(RECOGNIZE_LOGIC_CASES);
		// if (settings.recognizeExtremumInSolver)
		implem().currParameters.remove(RECOGNIZE_EXTREMUM_CASES);
		// if (settings.recognizeSumInSolver)
		implem().currParameters.remove(RECOGNIZE_SUM_CASES);
		try {
			if (imp().head.control.general.verbose > 1)
				XParser.VERBOSE = true;
			if (settings.discardedClasses.indexOf(',') < 0)
				loadInstance(name(), settings.discardedClasses);
			else
				loadInstance(name(), settings.discardedClasses.split(","));
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("Problem when parsing the instance. Fix the problem.");
			System.exit(1);
		}
	}

	@Override
	public Problem imp() {
		return (Problem) api2imp.get(this);
	}

	@Override
	public void beginInstance(TypeFramework type) {
		if (type == TypeFramework.COP)
			imp().head.control.toCOP();
	}

	private void copyBasicAttributes(ModelingEntity entity, ParsingEntry entry) {
		if (entry.id != null)
			entity.id(entry.id);
		if (entry.note != null)
			entity.note(entry.note);
		if (entry.classes != null)
			entity.tag(entry.classes);
	}

	private Problem pb;

	// public XCSP3() {
	// this.pb = imp();
	// }

	/**********************************************************************************************
	 * Methods for transforming (mapping) parser objects into solver objects ; tr = tr(ansform)
	 *********************************************************************************************/

	private Map<XVar, Variable> mapVar = new LinkedHashMap<>();

	private VariableInteger trVar(IVar x) {
		return (VariableInteger) mapVar.get(x);
	}

	private VariableInteger trVar(XVarInteger x) {
		return (VariableInteger) mapVar.get(x);
	}

	private VariableSymbolic trVar(XVarSymbolic x) {
		return (VariableSymbolic) mapVar.get(x);
	}

	private Condition trVar(Condition condition) {
		return condition instanceof ConditionVar ? new ConditionVar(((ConditionVar) condition).operator, trVar(((ConditionVar) condition).x)) : condition;
	}

	private XNode<IVar> trVar(XNode<XVarInteger> tree) {
		return ((XNode) tree).replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v);
	}

	private XNode<IVar> trVarSymbolic(XNode<XVarSymbolic> tree) {
		return ((XNode) tree).replaceLeafValues(v -> v instanceof XVarSymbolic ? trVar((XVarSymbolic) v) : v);
	}

	private XNode<IVar>[] trVar(XNode<XVarInteger>[] trees) {
		return Stream.of(trees).map(t -> t.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v)).toArray(XNode[]::new);
	}

	private VariableInteger[] trVars(XVarInteger[] t) {
		return Arrays.stream(t).map(v -> mapVar.get(v)).toArray(VariableInteger[]::new);
	}

	private VariableInteger[][] trVars2D(XVarInteger[][] m) {
		return Arrays.stream(m).map(t -> trVars(t)).toArray(VariableInteger[][]::new);
	}

	private VariableSymbolic[] trVars(XVarSymbolic[] t) {
		return Arrays.stream(t).map(v -> mapVar.get(v)).toArray(VariableSymbolic[]::new);
	}

	// private VariableSymbolic[][] trVars2D(XVarSymbolic[][] m) {
	// return Arrays.stream(m).map(t -> trVars(t)).toArray(VariableSymbolic[][]::new);
	// }

	// private Variable[] trVars(Object vars) {
	// return Arrays.stream((XVar[]) vars).map(v -> mapVar.get(v)).toArray(Variable[]::new);
	// }

	// private Variable[][] trVars2D(Object vars) {
	// return Arrays.stream((XVar[][]) vars).map(t -> trVars(t)).toArray(Variable[][]::new);
	// }

	/**********************************************************************************************
	 * Methods for loading variables, constraints and objectives
	 *********************************************************************************************/

	@Override
	public void loadVar(XVar v) {
		implem().manageIdFor(v);
		if (v.degree > 0) {
			if (v.dom instanceof Dom)
				mapVar.put(v, (VariableInteger) var(v.id, (Dom) v.dom, v.note, v.classes));
			else if (v.dom instanceof DomSymbolic)
				mapVar.put(v, (VariableSymbolic) var(v.id, (DomSymbolic) v.dom, v.note, v.classes));
			else
				unimplementedCase(v);
		}
	}

	// method for mapping variables inside arrays
	private void completeMapVar(XArray va, Object a, int... indexes) {
		if (a != null)
			if (a.getClass().isArray())
				IntStream.range(0, Array.getLength(a)).forEach(i -> completeMapVar(va, Array.get(a, i), vals(indexes, i)));
			else
				mapVar.put(va.varAt(indexes), (Variable) a);
	}

	@Override
	public void loadArray(XArray va) {
		implem().manageIdFor(va);
		Object a = null;
		int[] sz = va.size;
		if (va.getType() == TypeVar.integer) {
			if (sz.length == 1)
				a = array(va.id, size(sz[0]), i -> va.domAt(i), va.note, va.classes);
			else if (sz.length == 2)
				a = array(va.id, size(sz[0], sz[1]), (i, j) -> va.domAt(i, j), va.note, va.classes);
			else if (sz.length == 3)
				a = array(va.id, size(sz[0], sz[1], sz[2]), (i, j, k) -> va.domAt(i, j, k), va.note, va.classes);
			else if (sz.length == 4)
				a = array(va.id, size(sz[0], sz[1], sz[2], sz[3]), (i, j, k, l) -> va.domAt(i, j, k, l), va.note, va.classes);
			else if (sz.length == 5)
				a = array(va.id, size(sz[0], sz[1], sz[2], sz[3], sz[4]), (i, j, k, l, m) -> va.domAt(i, j, k, l, m), va.note, va.classes);
			else
				unimplementedCase(va);
		} else if (va.getType() == TypeVar.symbolic) {
			if (sz.length == 1)
				a = arraySymbolic(va.id, size(sz[0]), i -> va.varAt(i) != null && va.varAt(i).degree > 0 ? (DomSymbolic) va.varAt(i).dom : null, va.note,
						va.classes);
			else
				unimplementedCase(va);
		} else
			unimplementedCase(va);
		completeMapVar(va, a);
	}

	@Override
	public void buildVarInteger(XVarInteger x, int minValue, int maxValue) {
		throw new AssertionError();
	}

	@Override
	public void buildVarInteger(XVarInteger x, int[] values) {
		throw new AssertionError();
	}

	@Override
	public void buildVarSymbolic(XVarSymbolic x, String[] values) {
		throw new AssertionError();
	}

	/**********************************************************************************************
	 * Methods for loading constraints
	 *********************************************************************************************/

	@Override
	public void loadBlock(XBlock block) {
		CtrEntity entity = block(() -> loadConstraints(block.subentries)); // recursive call
		copyBasicAttributes(entity, block);
	}

	@Override
	public void loadGroup(XGroup group) {
		CtrEntity entity = imp().manageLoop(() -> {
			if (group.template instanceof XCtr)
				loadCtrs((XCtr) group.template, group.argss, group);
			else if (group.template instanceof XLogic && ((XLogic) group.template).getType() == TypeCtr.not) {
				CEntry child = ((XLogic) group.template).components[0];
				if (child instanceof XCtr && ((XCtr) child).type == TypeCtr.allEqual)
					Stream.of(group.argss).forEach(o -> notAllEqual(trVars((XVarInteger[]) o)));
				else
					unimplementedCase(group);
			} else
				unimplementedCase(group);
		});
		if (entity != null)
			copyBasicAttributes(entity, group);
	}

	@Override
	public void loadSlide(XSlide s) {
		CtrArray entity = imp().manageLoop(() -> XCallbacks2.super.loadSlide(s));
		copyBasicAttributes(entity, s);
	}

	@Override
	public void beginLogic(XLogic l) {
		System.out.println("Begin : " + l);
	}

	@Override
	public void endLogic(XLogic l) {
		System.out.println("End : " + l);
	}

	@Override
	public void loadCtr(XCtr c) {
		if (imp().features.mustDiscard(c.vars()))
			return;
		if (imp().head.control.constraints.ignoredCtrType == c.type) {
			imp().features.nDiscardedCtrs++;
			return;
		}
		if (imp().head.control.constraints.ignoreCtrArity == c.vars().length) {
			imp().features.nDiscardedCtrs++;
			return;
		}
		int sizeBefore = imp().ctrEntities.allEntities.size();

		XCallbacks2.super.loadCtr(c);
		if (sizeBefore == imp().ctrEntities.allEntities.size())
			return; // must have been a true constraint (should be checked)
		CtrEntity entity = imp().ctrEntities.allEntities.get(imp().ctrEntities.allEntities.size() - 1);
		copyBasicAttributes(entity, c);
	}

	@Override
	public void buildCtrFalse(String id, XVar[] list) {
		if (imp().settings.framework == TypeFramework.MAXCSP)
			imp().addCtr(new CtrHardFalse(imp(), trVars(Stream.of(list).map(x -> (XVarInteger) x).toArray(XVarInteger[]::new)), "CtrHard False for MaxCSP"));
		// extension((VarInteger[]) trVars(Stream.of(list).map(x -> (XVarInteger) x).toArray(XVarInteger[]::new)), new int[][] { {} });
		else
			throw new RuntimeException("Constraint with only conflicts");
	}

	// ************************************************************************
	// ***** Constraint intension
	// ************************************************************************

	@Override
	public void buildCtrIntension(String id, XVarInteger[] scope, XNodeParent<XVarInteger> tree) {
		Kit.control(tree.exactlyVars(scope), "Pb with scope");
		pb.intension((XNodeParent<IVar>) trVar(tree));
	}

	// private int nPrimitiveCalls = 0;
	//
	// private void displayPrimitives(String s) {
	// if (imp().head.control.xml.displayPrimitives)
	// System.out.println((nPrimitiveCalls++ == 0 ? "\n" : "") + "Primitive in class XCSP3 : " + s);
	// }
	//
	// // unary primitives
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorRel op, int k) {
	// displayPrimitives(x + " " + op + " " + k);
	// repost(id); // imp().intension(XNodeParent.build(op.toExpr(), trVar(x), k));
	// }
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op, int[] t) {
	// displayPrimitives(x + " " + op + " " + Kit.join(t));
	// repost(id); // intension(op == IN ? in(trVar(x), set(t)) : notin(trVar(x), set(t)));
	// }
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op, int min, int max) {
	// displayPrimitives(x + " " + op + " " + min + ".." + max);
	// repost(id); // intension(op == IN ? and(ge(trVar(x), min), le(trVar(x), max)) : or(lt(trVar(x), min), gt(trVar(x), max)));
	// }
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int k1, TypeConditionOperatorRel op, int k2) {
	// displayPrimitives("(" + x + " " + aop + " " + k1 + ") " + op + " " + k2);
	// repost(id);
	// }
	//
	// // binary primitives
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, XVarInteger y, TypeConditionOperatorRel op, int k) {
	// displayPrimitives("(" + x + " " + aop + " " + y + ") " + op + " " + k);
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int k, TypeConditionOperatorRel op, XVarInteger y) {
	// displayPrimitives("(" + x + " " + aop + " " + k + ") " + op + " " + y);
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrLogic(String id, XVarInteger x, XVarInteger y, TypeConditionOperatorRel op, int k) {
	// displayPrimitives(x + " = (" + y + " " + op + " " + k + ")");
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeUnaryArithmeticOperator aop, XVarInteger y) {
	// displayPrimitives(x + " " + aop + " " + y);
	// repost(id);
	// }
	//
	// // ternary primitives
	//
	// @Override
	// public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, XVarInteger y, TypeConditionOperatorRel op, XVarInteger z) {
	// displayPrimitives("(" + x + " " + aop + " " + y + ") " + op + " " + z);
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrLogic(String id, XVarInteger x, XVarInteger y, TypeConditionOperatorRel op, XVarInteger z) {
	// displayPrimitives(x + " = (" + y + " " + op + " " + z + ")");
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrLogic(String id, TypeLogicalOperator lop, XVarInteger[] vars) {
	// assert Stream.of(vars).allMatch(x -> x.isZeroOne());
	// displayPrimitives(lop + " " + Kit.join(vars));
	// repost(id);
	// }
	//
	// @Override
	// public void buildCtrLogic(String id, XVarInteger x, TypeEqNeOperator op, TypeLogicalOperator lop, XVarInteger[] vars) {
	// assert Stream.of(vars).allMatch(y -> y.isZeroOne());
	// displayPrimitives(x + " " + op + " " + lop + " " + Kit.join(vars));
	// repost(id);
	// }

	// ************************************************************************
	// ***** Constraint extension
	// ************************************************************************

	@Override
	public void buildCtrExtension(String id, XVarInteger x, int[] values, boolean positive, Set<TypeFlag> flags) {
		control(!flags.contains(TypeFlag.STARRED_TUPLES));
		if (flags.contains(TypeFlag.UNCLEAN_TUPLES))
			values = Variable.filterValues(trVar(x), values, false);
		pb.extension(vars(trVar(x)), dub(values), positive);
	}

	@Override
	public void buildCtrExtension(String id, XVarInteger[] list, int[][] tuples, boolean positive, Set<TypeFlag> flags) {
		if (flags.contains(TypeFlag.UNCLEAN_TUPLES))
			tuples = Variable.filterTuples(trVars(list), tuples, false);
		pb.extension(trVars(list), tuples, positive, flags.contains(TypeFlag.STARRED_TUPLES));
	}

	@Override
	public void buildCtrExtension(String id, XVarInteger[] list, AbstractTuple[] tuples, boolean positive, Set<TypeFlag> flags) {
		pb.extension(trVars(list), tuples, positive);
	}

	// ************************************************************************
	// ***** Constraints Regular and Mdd
	// ************************************************************************

	@Override
	public void buildCtrRegular(String id, XVarInteger[] list, Object[][] transitions, String startState, String[] finalStates) {
		Transition[] ts = Stream.of(transitions).map(t -> new Transition((String) t[0], t[1], (String) t[2])).toArray(Transition[]::new);
		imp().regular(trVars(list), new Automaton(startState, ts, finalStates));
	}

	@Override
	public void buildCtrMDD(String id, XVarInteger[] list, Object[][] transitions) {
		Transition[] ts = Stream.of(transitions).map(t -> new Transition((String) t[0], t[1], (String) t[2])).toArray(Transition[]::new);
		imp().mdd(trVars(list), ts);
	}

	// ************************************************************************
	// ***** Constraints AllDifferent and AllEqual
	// ************************************************************************

	@Override
	public void buildCtrAllDifferent(String id, XVarInteger[] list) {
		imp().allDifferent(trVars(list));
	}

	@Override
	public void buildCtrAllDifferentExcept(String id, XVarInteger[] list, int[] except) {
		imp().allDifferent(trVars(list), except);
	}

	@Override
	public void buildCtrAllDifferentList(String id, XVarInteger[][] lists) {
		imp().allDifferentList(trVars2D(lists));
	}

	@Override
	public void buildCtrAllDifferentMatrix(String id, XVarInteger[][] matrix) {
		imp().allDifferentMatrix(trVars2D(matrix));
	}

	@Override
	public void buildCtrAllDifferent(String id, XNode<XVarInteger>[] trees) {
		imp().allDifferent(trVar(trees));
	}

	@Override
	public void buildCtrAllEqual(String id, XVarInteger[] list) {
		imp().allEqual(trVars(list));
	}

	// ************************************************************************
	// ***** Constraint ordered/lexicographic
	// ************************************************************************

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, TypeOperatorRel operator) {
		imp().ordered(trVars(list), new int[list.length - 1], operator);
	}

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, int[] lengths, TypeOperatorRel operator) {
		imp().ordered(trVars(list), lengths, operator);
	}

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, XVarInteger[] lengths, TypeOperatorRel operator) {
		imp().ordered(trVars(list), trVars(lengths), operator);
	}

	@Override
	public void buildCtrLex(String id, XVarInteger[][] lists, TypeOperatorRel operator) {
		imp().lex(trVars2D(lists), operator);
	}

	@Override
	public void buildCtrLexMatrix(String id, XVarInteger[][] matrix, TypeOperatorRel operator) {
		imp().lexMatrix(trVars2D(matrix), operator);
	}

	// ************************************************************************
	// ***** Constraint sum
	// ************************************************************************

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, Condition condition) {
		imp().sum(trVars(list), repeat(1, list.length), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, int[] coeffs, Condition condition) {
		imp().sum(trVars(list), coeffs, trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, XVarInteger[] coeffs, Condition condition) {
		imp().sum(trVars(list), trVars(coeffs), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		imp().sum(trVar(trees), repeat(1, trees.length), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XNode<XVarInteger>[] trees, int[] coeffs, Condition condition) {
		assert coeffs != null;
		imp().sum(trVar(trees), coeffs, trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XNode<XVarInteger>[] trees, XVarInteger[] coeffs, Condition condition) {
		unimplementedCase(id, join(trees), join(coeffs), condition); // TODO
	}

	// ************************************************************************
	// ***** Constraint count
	// ************************************************************************

	@Override
	public void buildCtrCount(String id, XVarInteger[] list, int[] values, Condition condition) {
		imp().count(trVars(list), values, trVar(condition));
	}

	@Override
	public void buildCtrCount(String id, XVarInteger[] list, XVarInteger[] values, Condition condition) {
		imp().count(trVars(list), trVars(values), trVar(condition));
	}

	@Override
	public void buildCtrAtLeast(String id, XVarInteger[] list, int value, int k) {
		imp().count(trVars(list), new int[] { value }, condition(GE, k));
		// atLeast(trVars(list), value, k);
	}

	@Override
	public void buildCtrAtMost(String id, XVarInteger[] list, int value, int k) {
		imp().count(trVars(list), new int[] { value }, condition(LE, k));
		// atMost(trVars(list), value, k);
	}

	@Override
	public void buildCtrExactly(String id, XVarInteger[] list, int value, int k) {
		imp().count(trVars(list), new int[] { value }, condition(EQ, k)); // exactly(trVars(list), value, k);
	}

	@Override
	public void buildCtrExactly(String id, XVarInteger[] list, int value, XVarInteger k) {
		imp().count(trVars(list), new int[] { value }, trVar(condition(EQ, k))); // exactly(trVars(list), value, trVar(k));
	}

	@Override
	public void buildCtrAmong(String id, XVarInteger[] list, int[] values, int k) {
		imp().count(trVars(list), values, condition(EQ, k)); // among(trVars(list), values, k);
	}

	@Override
	public void buildCtrAmong(String id, XVarInteger[] list, int[] values, XVarInteger k) {
		imp().count(trVars(list), values, trVar(condition(EQ, k))); // unimplementedCase(id, Utilities.join(list), Utilities.join(values), k);
	}

	@Override
	public void buildCtrNValues(String id, XVarInteger[] list, Condition condition) {
		imp().nValues(trVars(list), trVar(condition));
	}

	@Override
	public void buildCtrNValuesExcept(String id, XVarInteger[] list, int[] values, Condition condition) {
		imp().nValues(trVars(list), trVar(condition), values);
	}

	@Override
	public void buildCtrNotAllEqual(String id, XVarInteger[] list) {
		buildCtrNValues(id, list, condition(GT, 1));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, XVarInteger[] occurs) {
		imp().cardinality(trVars(list), values, closed, trVars(occurs));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, int[] occurs) {
		imp().cardinality(trVars(list), values, closed, occurs);
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, int[] occursMin, int[] occursMax) {
		imp().cardinality(trVars(list), values, closed, occursMin, occursMax);
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, XVarInteger[] occurs) {
		imp().cardinality(trVars(list), trVars(values), closed, trVars(occurs));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, int[] occurs) {
		imp().cardinality(trVars(list), trVars(values), closed, occurs);
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, int[] occursMin, int[] occursMax) {
		imp().cardinality(trVars(list), trVars(values), closed, occursMin, occursMax);
	}

	@Override
	public void buildCtrMaximum(String id, XVarInteger[] list, Condition condition) {
		imp().maximum(trVars(list), trVar(condition));
	}

	@Override
	public void buildCtrMaximum(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, Condition condition) {
		unimplementedCase(id, Utilities.join(list), startIndex, index, rank, condition);
	}

	@Override
	public void buildCtrMaximum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		imp().maximum(trVar(trees), trVar(condition));
	}

	@Override
	public void buildCtrMinimum(String id, XVarInteger[] list, Condition condition) {
		imp().minimum(trVars(list), trVar(condition));
	}

	@Override
	public void buildCtrMinimum(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, Condition condition) {
		unimplementedCase(id, Utilities.join(list), startIndex, index, rank, condition);
	}

	@Override
	public void buildCtrMinimum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		imp().minimum(trVar(trees), trVar(condition));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int value) {
		imp().element(trVars(list), value);
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, XVarInteger value) {
		imp().element(trVars(list), trVar(value));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, XVarInteger value) {
		control(startIndex == 0 && rank == TypeRank.ANY);
		imp().element(trVars(list), startIndex, trVar(index), rank, trVar(value));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, int value) {
		control(startIndex == 0 && rank == TypeRank.ANY);
		imp().element(trVars(list), startIndex, trVar(index), rank, value);
	}

	@Override
	public void buildCtrElement(String id, int[] list, int startIndex, XVarInteger index, TypeRank rank, XVarInteger value) {
		control(rank == TypeRank.ANY);
		imp().element(list, startIndex, trVar(index), rank, trVar(value));
	}

	@Override
	public void buildCtrElement(String id, int[][] matrix, int startRowIndex, XVarInteger rowIndex, int startColIndex, XVarInteger colIndex,
			XVarInteger value) {
		control(startRowIndex == 0 && startColIndex == 0);
		imp().element(matrix, startRowIndex, trVar(rowIndex), startColIndex, trVar(colIndex), trVar(value));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[][] matrix, int startRowIndex, XVarInteger rowIndex, int startColIndex, XVarInteger colIndex,
			int value) {
		control(startRowIndex == 0 && startColIndex == 0);
		imp().element(trVars2D(matrix), startRowIndex, trVar(rowIndex), startColIndex, trVar(colIndex), value);
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list, int startIndex) {
		imp().channel(trVars(list), startIndex);
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list1, int startIndex1, XVarInteger[] list2, int startIndex2) {
		imp().channel(trVars(list1), startIndex1, trVars(list2), startIndex2);
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list, int startIndex, XVarInteger value) {
		imp().channel(trVars(list), startIndex, trVar(value));
	}

	@Override
	public void buildCtrStretch(String id, XVarInteger[] list, int[] values, int[] widthsMin, int[] widthsMax) {
		imp().stretch(trVars(list), values, widthsMin, widthsMax, null);
	}

	@Override
	public void buildCtrStretch(String id, XVarInteger[] list, int[] values, int[] widthsMin, int[] widthsMax, int[][] patterns) {
		imp().stretch(trVars(list), values, widthsMin, widthsMax, patterns);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[] origins, int[] lengths, boolean zeroIgnored) {
		imp().noOverlap(trVars(origins), lengths, zeroIgnored);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[] origins, XVarInteger[] lengths, boolean zeroIgnored) {
		imp().noOverlap(trVars(origins), trVars(lengths), zeroIgnored);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[][] origins, int[][] lengths, boolean zeroIgnored) {
		imp().noOverlap(trVars2D(origins), lengths, zeroIgnored);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[][] origins, XVarInteger[][] lengths, boolean zeroIgnored) {
		imp().noOverlap(trVars2D(origins), trVars2D(lengths), zeroIgnored);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, int[] heights, Condition condition) {
		imp().cumulative(trVars(origins), lengths, null, heights, trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] heights, Condition condition) {
		imp().cumulative(trVars(origins), lengths, null, trVars(heights), trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, int[] heights, Condition condition) {
		imp().cumulative(trVars(origins), trVars(lengths), null, heights, trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] heights, Condition condition) {
		imp().cumulative(trVars(origins), trVars(lengths), null, trVars(heights), trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] ends, int[] heights, Condition condition) {
		imp().cumulative(trVars(origins), lengths, trVars(ends), heights, trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
		imp().cumulative(trVars(origins), lengths, trVars(ends), trVars(heights), trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] ends, int[] heights, Condition condition) {
		imp().cumulative(trVars(origins), trVars(lengths), trVars(ends), heights, trVar(condition));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
		imp().cumulative(trVars(origins), trVars(lengths), trVars(ends), trVars(heights), trVar(condition));
	}

	@Override
	public void buildCtrInstantiation(String id, XVarInteger[] list, int[] values) {
		imp().instantiation(trVars(list), values);
	}

	@Override
	public void buildCtrClause(String id, XVarInteger[] pos, XVarInteger[] neg) {
		imp().clause(trVars(pos), trVars(neg));
	}

	@Override
	public void buildCtrCircuit(String id, XVarInteger[] list, int startIndex) {
		imp().circuit(trVars(list), startIndex);
	}

	@Override
	public void buildBinPacking(String id, XVarInteger[] list, int[] sizes, Condition condition) {
		if (condition instanceof ConditionVal && (((ConditionVal) condition).operator == LT || ((ConditionVal) condition).operator == LE))
			imp().addCtr(new BinPackingSimple(imp(), trVars(list), sizes,
					Utilities.safeInt(((ConditionVal) condition).k) - (((ConditionVal) condition).operator == LT ? 1 : 0)));
		else
			unimplementedCase(id, Utilities.join(list), Utilities.join(sizes), condition);
	}

	/**********************************************************************************************
	 * Methods for loading objectives
	 *********************************************************************************************/

	@Override
	public void loadObj(XObj o) {
		if (imp().features.mustDiscard(o.vars()))
			return;
		XCallbacks2.super.loadObj(o);
		CtrEntity entity = imp().ctrEntities.allEntities.get(imp().ctrEntities.allEntities.size() - 1);
		copyBasicAttributes(entity, o);
	}

	@Override
	public void buildObjToMinimize(String id, XVarInteger x) {
		imp().minimize(trVar(x));
	}

	@Override
	public void buildObjToMaximize(String id, XVarInteger x) {
		imp().maximize(trVar(x));
	}

	static class VarVal {
		Variable x;
		int a;

		VarVal(Variable x, int a) {
			this.x = x;
			this.a = a;
		}
	}

	private List<VarVal> isSum(XNodeParent<XVarInteger> tree) {
		List<VarVal> list = new ArrayList<>();
		if (tree.type == TypeExpr.ADD)
			for (XNode<XVarInteger> son : tree.sons) {
				if (son.type == TypeExpr.VAR)
					list.add(new VarVal(trVar(son.var(0)), 1));
				else if (MatcherInterface.x_mul_k.matches(son) || MatcherInterface.k_mul_x.matches(son))
					list.add(new VarVal(trVar(son.var(0)), son.val(0)));
				else {
					list.clear();
					break;
				}
			}
		return list;
	}

	@Override
	public void buildObjToMinimize(String id, XNodeParent<XVarInteger> tree) {
		List<VarVal> list = isSum(tree);
		if (list.size() > 0)
			imp().minimize(SUM, list.stream().map(vv -> vv.x).toArray(VariableInteger[]::new), list.stream().mapToInt(vv -> vv.a).toArray());
		else
			imp().minimize(trVar(tree));
	}

	@Override
	public void buildObjToMaximize(String id, XNodeParent<XVarInteger> tree) {
		List<VarVal> list = isSum(tree);
		if (list.size() > 0)
			imp().maximize(SUM, list.stream().map(vv -> vv.x).toArray(VariableInteger[]::new), list.stream().mapToInt(vv -> vv.a).toArray());
		else
			imp().maximize(trVar(tree));
	}

	@Override
	public void buildObjToMinimize(String id, TypeObjective type, XVarInteger[] list) {
		imp().minimize(type, trVars(list));
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XVarInteger[] list) {
		imp().maximize(type, trVars(list));
	}

	@Override
	public void buildObjToMinimize(String id, TypeObjective type, XVarInteger[] list, int[] coeffs) {
		imp().minimize(type, trVars(list), coeffs);
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XVarInteger[] list, int[] coeffs) {
		imp().maximize(type, trVars(list), coeffs);
	}

	@Override
	public void buildObjToMinimize(String id, TypeObjective type, XNode<XVarInteger>[] trees) {
		imp().minimize(type, trVar(trees));
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees) {
		imp().maximize(type, trVar(trees));
	}

	@Override
	public void buildObjToMinimize(String id, TypeObjective type, XNode<XVarInteger>[] trees, int[] coeffs) {
		imp().minimize(type, trVar(trees), coeffs);
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees, int[] coeffs) {
		imp().maximize(type, trVar(trees), coeffs);
	}

	/**********************************************************************************************
	 ***** Methods to be implemented on symbolic variables/constraints
	 *********************************************************************************************/

	@Override
	public void buildCtrIntension(String id, XVarSymbolic[] scope, XNodeParent<XVarSymbolic> tree) {
		control(tree.exactlyVars(scope), "Pb with scope");
		imp().intension((XNodeParent<IVar>) trVarSymbolic(tree));
		// imp().intension(trVars(scope), (XNodeParent<IVar>) (Object) tree);
	}

	@Override
	public void buildCtrExtension(String id, XVarSymbolic x, String[] values, boolean positive, Set<TypeFlag> flags) {
		control(!flags.contains(TypeFlag.STARRED_TUPLES), "Forbidden for unary constraints");
		values = flags.contains(TypeFlag.UNCLEAN_TUPLES) ? Variable.filterValues(trVar(x), values) : values;
		imp().extension(vars(trVar(x)), dub(values), positive);
	}

	@Override
	public void buildCtrExtension(String id, XVarSymbolic[] list, String[][] tuples, boolean positive, Set<TypeFlag> flags) {
		tuples = flags.contains(TypeFlag.UNCLEAN_TUPLES) ? Variable.filterTuples(trVars(list), tuples) : tuples;
		imp().extension(trVars(list), tuples, positive, flags.contains(TypeFlag.STARRED_TUPLES));
	}

	@Override
	public void buildCtrAllDifferent(String id, XVarSymbolic[] list) {
		imp().allDifferent(trVars(list));
	}

	/**********************************************************************************************
	 * Methods to be implemented on Annotations
	 *********************************************************************************************/

	@Override
	public void buildAnnotationDecision(XVarInteger[] list) {
		decisionVariables(trVars(list));
	}

}
