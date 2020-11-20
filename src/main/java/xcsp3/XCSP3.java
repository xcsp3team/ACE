package xcsp3;

import static org.xcsp.common.Types.TypeArithmeticOperator.ADD;
import static org.xcsp.common.Types.TypeArithmeticOperator.DIST;
import static org.xcsp.common.Types.TypeArithmeticOperator.MOD;
import static org.xcsp.common.Types.TypeArithmeticOperator.MUL;
import static org.xcsp.common.Types.TypeArithmeticOperator.SUB;
import static org.xcsp.common.Utilities.join;
import static org.xcsp.common.Utilities.safeInt;

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
import org.xcsp.common.Condition.ConditionRel;
import org.xcsp.common.Condition.ConditionVal;
import org.xcsp.common.Condition.ConditionVar;
import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeArithmeticOperator;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeCtr;
import org.xcsp.common.Types.TypeEqNeOperator;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Types.TypeFlag;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeLogicalOperator;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.Types.TypeUnaryArithmeticOperator;
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
import constraints.intension.PrimitiveBinary.PrimitiveBinaryAdd;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryDist;
import constraints.intension.PrimitiveBinary.PrimitiveBinaryLog;
import constraints.intension.PrimitiveBinary.PrimitiveBinarySub;
import constraints.intension.PrimitiveBinary.PrimitiveBinarySub.SubEQ2;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryAdd;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryLog;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryMod;
import constraints.intension.PrimitiveTernary.PrimitiveTernaryMul;
import dashboard.Arguments;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.Variable.VariableInteger;
import variables.Variable.VariableSymbolic;

/**
 * This class corresponds to a problem loading instances in XCSP3 format.
 */
public class XCSP3 implements ProblemAPI, XCallbacks2 {

	private Implem implem = new Implem(this);

	@Override
	public Implem implem() {
		return implem;
	}

	private List<String> listOfFileNames;

	@Override
	public String name() {
		return listOfFileNames.get(((Problem) imp()).head.instanceNumber);
	}

	private List<String> collect(List<String> list, File f) {
		if (f.isDirectory())
			Stream.of(f.listFiles()).forEach(g -> collect(list, g));
		else if (Stream.of(".xml", ".lzma").anyMatch(suf -> f.getName().endsWith(suf)))
			list.add(f.getAbsolutePath());
		return list;
	}

	public void data() {
		String fileName = imp().askString("File or directory:");
		if (listOfFileNames == null) {
			listOfFileNames = collect(new ArrayList<>(), new File(fileName)).stream().sorted().collect(Collectors.toList());
			Arguments.nInstancesToSolve = listOfFileNames.size();
		}
		((Problem) imp()).parameters.get(0).setValue(name());
		System.out.println();
	}

	@Override
	public void model() {
		try {
			// Kit.log.info("Discarded classes " + imp().rs.cp.settingXml.discardedClasses);
			if (imp().head.control.settingGeneral.verbose > 1)
				XParser.VERBOSE = true;
			if (imp().head.control.settingXml.discardedClasses.indexOf(',') < 0)
				loadInstance(name(), imp().head.control.settingXml.discardedClasses);
			else
				loadInstance(name(), imp().head.control.settingXml.discardedClasses.split(",")); // imp().rs.cp.xml.discardedClasses.split(","));
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

	/**********************************************************************************************
	 * Methods for transforming (mapping) parser objects into solver objects ; tr = tr(ansform)
	 *********************************************************************************************/

	private Map<XVar, Variable> mapVar = new LinkedHashMap<>();

	// private Object trDom(XDom xd, Map<XDom, Object> cache4DomObject) {
	// Object dom = cache4DomObject.get(xd);
	// if (dom == null) {
	// Object o = XCallbacks.trDom(xd);
	// if (o instanceof int[])
	// dom = (int[]) o;
	// else if (o instanceof String[])
	// dom = (String[]) o;
	// else {
	// dom = (IntegerInterval) o;
	// }
	// cache4DomObject.put(xd, dom);
	// }
	// return dom;
	// }

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
		if (condition instanceof ConditionVar)
			return new ConditionVar(((ConditionVar) condition).operator, trVar(((ConditionVar) condition).x));
		return condition;
	}

	private XNode<IVar> trVar(XNode<IVar> tree) {
		return tree.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v);
	}

	private XNode<IVar>[] trVar(XNode<IVar>[] trees) {
		return Stream.of(trees).map(t -> t.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v)).toArray(XNode[]::new);
	}

	// private Variable trVar(Object var) {
	// return mapVar.get((XVar) var);
	// }

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
		if (imp().stuff.mustDiscard(c.vars()))
			return;
		if (imp().head.control.settingCtrs.ignoredCtrType == c.type) {
			imp().stuff.nDiscardedCtrs++;
			return;
		}
		if (imp().head.control.settingCtrs.ignoreCtrArity == c.vars().length) {
			imp().stuff.nDiscardedCtrs++;
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

	private int nPrimitiveCalls = 0;

	private void displayPrimitives(String s) {
		if (imp().head.control.settingXml.displayPrimitives)
			System.out.println((nPrimitiveCalls++ == 0 ? "\n" : "") + "Primitive in class XCSP3 : " + s);
	}

	@Override
	public CtrEntity intension(XNodeParent<IVar> tree) {
		// using a cache below ?
		XNodeParent<IVar> validTree = (XNodeParent<IVar>) tree
				.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v instanceof XVarSymbolic ? trVar((XVarSymbolic) v) : v);
		return imp().intension(validTree);
	}

	@Override
	public void buildCtrIntension(String id, XVarInteger[] scope, XNodeParent<XVarInteger> tree) {
		Utilities.control(tree.exactlyVars(scope), "Pb with scope");
		intension((XNodeParent<IVar>) (Object) tree);
	}

	// unary primitives

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorRel op, int k) {
		displayPrimitives(x + " " + op + " " + k);
		imp().intension(XNodeParent.build(op.toExpr(), trVar(x), k));
	}

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op, int[] t) {
		displayPrimitives(x + " " + op + " " + Kit.join(t));
		intension(op == IN ? in(trVar(x), set(t)) : notin(trVar(x), set(t)));
	}

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op, int min, int max) {
		displayPrimitives(x + " " + op + " " + min + ".." + max);
		intension(op == IN ? and(ge(trVar(x), min), le(trVar(x), max)) : or(lt(trVar(x), min), gt(trVar(x), max)));
	}

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int k1, TypeConditionOperatorRel op, int k2) {
		displayPrimitives("(" + x + " " + aop + " " + k1 + ") " + op + " " + k2);
		repost(id);
	}

	// public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int k, TypeConditionOperatorSet op, int[] t) {
	// intension(XNodeParent.build(op.toExpr(), XNodeParent.build(aop.toExpr(), trVar(x), k), set(t)));
	// }

	// binary primitives

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeUnaryArithmeticOperator aop, XVarInteger y) {
		displayPrimitives(x + " " + aop + " " + y);
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else {
			repost(id);
		}
	}

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, XVarInteger y, TypeConditionOperatorRel op, int k) {
		displayPrimitives("(" + x + " " + aop + " " + y + ") " + op + " " + k);
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else {
			if (aop == ADD)
				PrimitiveBinaryAdd.buildFrom(imp(), trVar(x), trVar(y), op, k);
			else if (aop == SUB)
				PrimitiveBinarySub.buildFrom(imp(), trVar(x), trVar(y), op, k);
			else if (aop == DIST)
				PrimitiveBinaryDist.buildFrom(imp(), trVar(x), trVar(y), op, k);
			else
				repost(id);
		}
	}

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int k, TypeConditionOperatorRel op, XVarInteger y) {
		displayPrimitives("(" + x + " " + aop + " " + k + ") " + op + " " + y);
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else {

			if (op == EQ && (aop == ADD || aop == SUB))
				imp().addCtr(new SubEQ2(imp(), trVar(x), trVar(y), aop == ADD ? -k : k));
			else
				repost(id);
		}
	}

	// ternary primitives

	@Override
	public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, XVarInteger y, TypeConditionOperatorRel op, XVarInteger z) {
		displayPrimitives("(" + x + " " + aop + " " + y + ") " + op + " " + z);
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else {
			if (aop == ADD)
				PrimitiveTernaryAdd.buildFrom(imp(), trVar(x), trVar(y), op, trVar(z));
			else if (aop == MOD && op == EQ)
				PrimitiveTernaryMod.buildFrom(imp(), trVar(x), trVar(y), op, trVar(z));
			else if (aop == MUL && op == EQ && (trVar(x).dom.is01() || trVar(y).dom.is01()))
				PrimitiveTernaryMul.buildFrom(imp(), trVar(x), trVar(y), op, trVar(z));
			else
				repost(id);
		}
	}

	@Override
	public void buildCtrLogic(String id, TypeLogicalOperator lop, XVarInteger[] vars) {
		assert Stream.of(vars).allMatch(x -> x.isZeroOne());
		displayPrimitives(lop + " " + Kit.join(vars));
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else
			repost(id);
	}

	@Override
	public void buildCtrLogic(String id, XVarInteger x, TypeEqNeOperator op, TypeLogicalOperator lop, XVarInteger[] vars) {
		assert Stream.of(vars).allMatch(y -> y.isZeroOne());
		displayPrimitives(x + " " + op + " " + lop + " " + Kit.join(vars));
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else
			repost(id);
	}

	@Override
	public void buildCtrLogic(String id, XVarInteger x, XVarInteger y, TypeConditionOperatorRel op, int k) {
		displayPrimitives(x + " = (" + y + " " + op + " " + k + ")");
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else
			PrimitiveBinaryLog.buildFrom(imp(), trVar(x), trVar(y), op, k);
	}

	@Override
	public void buildCtrLogic(String id, XVarInteger x, XVarInteger y, TypeConditionOperatorRel op, XVarInteger z) {
		displayPrimitives(x + " = (" + y + " " + op + " " + z + ")");
		if (imp().head.control.settingCtrs.ignorePrimitives)
			repost(id);
		else
			PrimitiveTernaryLog.buildFrom(imp(), trVar(x), trVar(y), op, trVar(z));
	}

	// ************************************************************************
	// ***** Constraint extension
	// ************************************************************************

	@Override
	public void buildCtrExtension(String id, XVarInteger x, int[] values, boolean positive, Set<TypeFlag> flags) {
		Kit.control(!flags.contains(TypeFlag.STARRED_TUPLES));
		if (flags.contains(TypeFlag.UNCLEAN_TUPLES))
			values = Variable.filterValues(trVar(x), values, false);
		extension(trVar(x), values, positive);
	}

	@Override
	public void buildCtrExtension(String id, XVarInteger[] list, int[][] tuples, boolean positive, Set<TypeFlag> flags) {
		if (flags.contains(TypeFlag.UNCLEAN_TUPLES))
			tuples = Variable.filterTuples(trVars(list), tuples, false);
		imp().extension(trVars(list), tuples, positive, flags.contains(TypeFlag.STARRED_TUPLES));
	}

	@Override
	public void buildCtrExtension(String id, XVarInteger[] list, AbstractTuple[] tuples, boolean positive, Set<TypeFlag> flags) {
		imp().extension(trVars(list), tuples, positive);
	}

	@Override
	public void buildCtrRegular(String id, XVarInteger[] list, Object[][] transitions, String startState, String[] finalStates) {
		imp().regular(trVars(list), new Automaton(startState,
				Stream.of(transitions).map(t -> new Transition((String) t[0], t[1], (String) t[2])).toArray(Transition[]::new), finalStates));
	}

	@Override
	public void buildCtrMDD(String id, XVarInteger[] list, Object[][] transitions) {
		mdd(trVars(list), Stream.of(transitions).map(t -> new Transition((String) t[0], t[1], (String) t[2])).toArray(Transition[]::new));
	}

	@Override
	public void buildCtrAllDifferent(String id, XVarInteger[] list) {
		allDifferent(trVars(list));
	}

	@Override
	public void buildCtrAllDifferentExcept(String id, XVarInteger[] list, int[] except) {
		trVars(list);
		allDifferent(trVars(list), exceptValues(except));
	}

	@Override
	public void buildCtrAllDifferentList(String id, XVarInteger[][] lists) {
		allDifferentList(trVars2D(lists));
	}

	@Override
	public void buildCtrAllDifferentMatrix(String id, XVarInteger[][] matrix) {
		allDifferentMatrix(trVars2D(matrix));
	}

	@Override
	public void buildCtrAllDifferent(String id, XNode<XVarInteger>[] trees) {
		allDifferent(trVar((XNode[]) trees));
	}

	@Override
	public void buildCtrAllEqual(String id, XVarInteger[] list) {
		allEqual(trVars(list));
	}

	// ************************************************************************
	// ***** Constraint ordered/lexicographic
	// ************************************************************************

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, TypeOperatorRel operator) {
		ordered(trVars(list), operator);
	}

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, int[] lengths, TypeOperatorRel operator) {
		ordered(trVars(list), lengths, operator);
	}

	@Override
	public void buildCtrOrdered(String id, XVarInteger[] list, XVarInteger[] lengths, TypeOperatorRel operator) {
		ordered(trVars(list), trVars(lengths), operator);
	}

	@Override
	public void buildCtrLex(String id, XVarInteger[][] lists, TypeOperatorRel operator) {
		lex(trVars2D(lists), operator);
	}

	@Override
	public void buildCtrLexMatrix(String id, XVarInteger[][] matrix, TypeOperatorRel operator) {
		lexMatrix(trVars2D(matrix), operator);
	}

	// ************************************************************************
	// ***** Constraint sum
	// ************************************************************************

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, Condition condition) {
		sum(trVars(list), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, int[] coeffs, Condition condition) {
		assert coeffs != null;
		sum(trVars(list), coeffs, trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XVarInteger[] list, XVarInteger[] coeffs, Condition condition) {
		sum(trVars(list), trVars(coeffs), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		sum(trVar((XNode[]) trees), trVar(condition));
	}

	@Override
	public void buildCtrSum(String id, XNode<XVarInteger>[] trees, int[] coeffs, Condition condition) {
		assert coeffs != null;
		sum(trVar((XNode[]) trees), coeffs, trVar(condition));
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
		if (condition instanceof ConditionVar)
			count(trVars(list), values, trVar(condition));
		else if (condition instanceof ConditionVal)
			count(trVars(list), values, ((ConditionRel) condition).operator, safeInt(((ConditionVal) condition).k));
		else
			unimplementedCase(id, Utilities.join(list), join(values), condition);
	}

	@Override
	public void buildCtrCount(String id, XVarInteger[] list, XVarInteger[] values, Condition condition) {
		unimplementedCase(id, Utilities.join(list), Utilities.join(values), condition);
	}

	@Override
	public void buildCtrAtLeast(String id, XVarInteger[] list, int value, int k) {
		atLeast(trVars(list), value, k);
	}

	@Override
	public void buildCtrAtMost(String id, XVarInteger[] list, int value, int k) {
		atMost(trVars(list), value, k);
	}

	@Override
	public void buildCtrExactly(String id, XVarInteger[] list, int value, int k) {
		exactly(trVars(list), value, k);
	}

	@Override
	public void buildCtrExactly(String id, XVarInteger[] list, int value, XVarInteger k) {
		exactly(trVars(list), value, trVar(k));
	}

	@Override
	public void buildCtrAmong(String id, XVarInteger[] list, int[] values, int k) {
		among(trVars(list), values, k);
	}

	@Override
	public void buildCtrAmong(String id, XVarInteger[] list, int[] values, XVarInteger k) {
		unimplementedCase(id, Utilities.join(list), Utilities.join(values), k);
	}

	@Override
	public void buildCtrNValues(String id, XVarInteger[] list, Condition condition) {
		if (condition instanceof ConditionVar)
			nValues(trVars(list), trVar(condition));
		else if (condition instanceof ConditionVal)
			nValues(trVars(list), ((ConditionRel) condition).operator, Utilities.safeInt(((ConditionVal) condition).k));
		else
			unimplementedCase(id, Utilities.join(list), condition);
	}

	@Override
	public void buildCtrNValuesExcept(String id, XVarInteger[] list, int[] values, Condition condition) {
		unimplementedCase(id, Utilities.join(list), Utilities.join(values), condition);
	}

	@Override
	public void buildCtrNotAllEqual(String id, XVarInteger[] list) {
		notAllEqual(trVars(list));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, XVarInteger[] occurs) {
		cardinality(trVars(list), values, closed, occurExactly(trVars(occurs)));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, int[] occurs) {
		cardinality(trVars(list), values, closed, occurExactly(occurs));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values, int[] occursMin, int[] occursMax) {
		cardinality(trVars(list), values, closed, occurBetween(occursMin, occursMax));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, XVarInteger[] occurs) {
		unimplementedCase(id, Utilities.join(list), closed, Utilities.join(values), Utilities.join(occurs));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, int[] occurs) {
		unimplementedCase(id, Utilities.join(list), closed, Utilities.join(values), Utilities.join(occurs));
	}

	@Override
	public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, XVarInteger[] values, int[] occursMin, int[] occursMax) {
		unimplementedCase(id, Utilities.join(list), closed, Utilities.join(values), Utilities.join(occursMin), Utilities.join(occursMax));
	}

	@Override
	public void buildCtrMaximum(String id, XVarInteger[] list, Condition condition) {
		if (condition instanceof ConditionVar && ((ConditionVar) condition).operator == EQ) {
			maximum(trVars(list), trVar(((ConditionVar) condition).x));
		} else if (condition instanceof ConditionVal) { // && ((ConditionVal) condition).operator == LT) {
			maximum(trVars(list), condition);
		} else
			unimplementedCase(id, Utilities.join(list), condition);
	}

	@Override
	public void buildCtrMaximum(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, Condition condition) {
		unimplementedCase(id, Utilities.join(list), startIndex, index, rank, condition);
	}

	@Override
	public void buildCtrMaximum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		XNode<IVar>[] validTrees = Stream.of(trees).map(t -> t.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v))
				.toArray(XNode[]::new);
		if (condition instanceof ConditionVar && ((ConditionVar) condition).operator == EQ)
			imp().maximum(validTrees, trVar(condition));
		else
			unimplementedCase(id, Utilities.join(trees), condition);
	}

	@Override
	public void buildCtrMinimum(String id, XVarInteger[] list, Condition condition) {
		if (condition instanceof ConditionVar && ((ConditionVar) condition).operator == EQ)
			minimum(trVars(list), trVar(((ConditionVar) condition).x));
		else
			unimplementedCase(id, Utilities.join(list), condition);
	}

	@Override
	public void buildCtrMinimum(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, Condition condition) {
		unimplementedCase(id, Utilities.join(list), startIndex, index, rank, condition);
	}

	@Override
	public void buildCtrMinimum(String id, XNode<XVarInteger>[] trees, Condition condition) {
		XNode<IVar>[] validTrees = Stream.of(trees).map(t -> t.replaceLeafValues(v -> v instanceof XVarInteger ? trVar((XVarInteger) v) : v))
				.toArray(XNode[]::new);
		if (condition instanceof ConditionVar && ((ConditionVar) condition).operator == EQ)
			imp().minimum(validTrees, trVar(condition));
		else
			unimplementedCase(id, Utilities.join(trees), condition);
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, XVarInteger value) {
		unimplementedCase(id, Utilities.join(list), value);
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int value) {
		unimplementedCase(id, Utilities.join(list), value);
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, XVarInteger value) {
		Kit.control(startIndex == 0 && rank == TypeRank.ANY);
		element(trVars(list), trVar(index), trVar(value));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[] list, int startIndex, XVarInteger index, TypeRank rank, int value) {
		control(startIndex == 0 && rank == TypeRank.ANY);
		element(trVars(list), trVar(index), value);
	}

	@Override
	public void buildCtrElement(String id, int[] list, int startIndex, XVarInteger index, TypeRank rank, XVarInteger value) {
		Kit.control(rank == TypeRank.ANY);
		element(list, startIndex(startIndex), index(trVar(index), rank), trVar(value));
	}

	@Override
	public void buildCtrElement(String id, int[][] matrix, int startRowIndex, XVarInteger rowIndex, int startColIndex, XVarInteger colIndex,
			XVarInteger value) {
		Kit.control(startRowIndex == 0 && startColIndex == 0);
		element(matrix, startRowIndex, trVar(rowIndex), startColIndex, trVar(colIndex), trVar(value));
	}

	@Override
	public void buildCtrElement(String id, XVarInteger[][] matrix, int startRowIndex, XVarInteger rowIndex, int startColIndex, XVarInteger colIndex,
			int value) {
		Kit.control(startRowIndex == 0 && startColIndex == 0);
		element(trVars2D(matrix), startRowIndex, trVar(rowIndex), startColIndex, trVar(colIndex), value);
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list, int startIndex) {
		unimplementedCase(id, Utilities.join(list), startIndex);
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list1, int startIndex1, XVarInteger[] list2, int startIndex2) {
		Kit.control(startIndex1 == 0 && startIndex2 == 0);
		channel(trVars(list1), trVars(list2));
	}

	@Override
	public void buildCtrChannel(String id, XVarInteger[] list, int startIndex, XVarInteger value) {
		Kit.control(startIndex == 0);
		channel(trVars(list), trVar(value));
	}

	@Override
	public void buildCtrStretch(String id, XVarInteger[] list, int[] values, int[] widthsMin, int[] widthsMax) {
		unimplementedCase(id, Utilities.join(list), Utilities.join(values), Utilities.join(widthsMin), Utilities.join(widthsMax));
	}

	@Override
	public void buildCtrStretch(String id, XVarInteger[] list, int[] values, int[] widthsMin, int[] widthsMax, int[][] patterns) {
		unimplementedCase(id, Utilities.join(list), Utilities.join(values), Utilities.join(widthsMin), Utilities.join(widthsMax), Utilities.join(patterns));
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[] origins, int[] lengths, boolean zeroIgnored) {
		if (!zeroIgnored)
			unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), zeroIgnored);
		noOverlap(trVars(origins), lengths);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[] origins, XVarInteger[] lengths, boolean zeroIgnored) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), zeroIgnored);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[][] origins, int[][] lengths, boolean zeroIgnored) {
		if (!zeroIgnored)
			unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), zeroIgnored);
		noOverlap(trVars2D(origins), lengths);
	}

	@Override
	public void buildCtrNoOverlap(String id, XVarInteger[][] origins, XVarInteger[][] lengths, boolean zeroIgnored) {
		if (!zeroIgnored)
			unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), zeroIgnored);
		noOverlap(trVars2D(origins), trVars2D(lengths));
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, int[] heights, Condition condition) {
		if (condition instanceof ConditionVal && (((ConditionVal) condition).operator == LT || ((ConditionVal) condition).operator == LE))
			cumulative(trVars(origins), lengths, heights,
					Utilities.safeInt(((ConditionVal) condition).k) - (((ConditionVal) condition).operator == LT ? 1 : 0));
		else
			unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, int[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] ends, int[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(ends), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(ends), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] ends, int[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(ends), Utilities.join(heights), condition);
	}

	@Override
	public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths, XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
		unimplementedCase(id, Utilities.join(origins), Utilities.join(lengths), Utilities.join(ends), Utilities.join(heights), condition);

	}

	@Override
	public void buildCtrInstantiation(String id, XVarInteger[] list, int[] values) {
		instantiation(trVars(list), values);
	}

	@Override
	public void buildCtrClause(String id, XVarInteger[] pos, XVarInteger[] neg) {
		clause(trVars(pos), trVars(neg));
	}

	@Override
	public void buildCtrCircuit(String id, XVarInteger[] list, int startIndex) {
		Kit.control(startIndex == 0);
		circuit(trVars(list));
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
		if (imp().stuff.mustDiscard(o.vars()))
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
			imp().minimize(trVar((XNode) tree));
	}

	@Override
	public void buildObjToMaximize(String id, XNodeParent<XVarInteger> tree) {
		List<VarVal> list = isSum(tree);
		if (list.size() > 0)
			imp().maximize(SUM, list.stream().map(vv -> vv.x).toArray(VariableInteger[]::new), list.stream().mapToInt(vv -> vv.a).toArray());
		else
			imp().maximize(trVar((XNode) tree));
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
		imp().minimize(type, trVar((XNode[]) trees));
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees) {
		imp().maximize(type, trVar((XNode[]) trees));
	}

	@Override
	public void buildObjToMinimize(String id, TypeObjective type, XNode<XVarInteger>[] trees, int[] coeffs) {
		imp().minimize(type, trVar((XNode[]) trees), coeffs);
	}

	@Override
	public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees, int[] coeffs) {
		imp().maximize(type, trVar((XNode[]) trees), coeffs);
	}

	/**********************************************************************************************
	 ***** Methods to be implemented on symbolic variables/constraints
	 *********************************************************************************************/

	@Override
	public void buildCtrIntension(String id, XVarSymbolic[] scope, XNodeParent<XVarSymbolic> tree) {
		Utilities.control(tree.exactlyVars(scope), "Pb with scope");
		intension((XNodeParent<IVar>) (Object) tree);
		// imp().intension(trVars(scope), (XNodeParent<IVar>) (Object) tree);
	}

	@Override
	public void buildCtrExtension(String id, XVarSymbolic x, String[] values, boolean positive, Set<TypeFlag> flags) {
		Kit.control(!flags.contains(TypeFlag.STARRED_TUPLES), () -> "Forbidden for unary constraints");
		values = flags.contains(TypeFlag.UNCLEAN_TUPLES) ? Variable.filterValues(trVar(x), values) : values;
		extension(trVar(x), values, positive);
	}

	@Override
	public void buildCtrExtension(String id, XVarSymbolic[] list, String[][] tuples, boolean positive, Set<TypeFlag> flags) {
		tuples = flags.contains(TypeFlag.UNCLEAN_TUPLES) ? Variable.filterTuples(trVars(list), tuples) : tuples;
		imp().extension(trVars(list), tuples, positive, flags.contains(TypeFlag.STARRED_TUPLES));
	}

	@Override
	public void buildCtrAllDifferent(String id, XVarSymbolic[] list) {
		allDifferent(trVars(list));
	}

	/**********************************************************************************************
	 * Methods to be implemented on Annotations
	 *********************************************************************************************/

	@Override
	public void buildAnnotationDecision(XVarInteger[] list) {
		decisionVariables(trVars(list));
	}

}
