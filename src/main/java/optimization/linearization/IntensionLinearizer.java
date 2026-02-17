/*
 * This file is part of the constraint solver ACE (AbsCon Essence).
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS.
 *
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization.linearization;

import org.ojalgo.optimisation.Expression;
import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;

import constraints.Constraint;
import constraints.ConstraintIntension;
import variables.Variable;

import java.util.HashMap;
import java.util.Map;

/**
 * Linearizer for general Intension (expression-tree) constraints.
 *
 * Handles constraints defined by Boolean expression trees when they represent
 * linear relationships. Parses the tree structure to extract linear forms.
 *
 * Supported patterns:
 * - le/lt/ge/gt/eq(linearExpr, constant) - linear comparisons
 * - le/lt/ge/gt/eq(x, y) - variable comparisons
 * - imp(b, linearConstraint) - implications (with big-M)
 * - or(constraint1, constraint2) - disjunctions (with big-M)
 *
 * Where linearExpr can be: var, add(x,y), sub(x,y), neg(x), mul(x,const), etc.
 */
public class IntensionLinearizer implements ConstraintLinearizer {

    // Statistics for debugging (tracks unhandled patterns)
    private static final Map<String, Integer> skippedPatterns = new HashMap<>();

    @Override
    public boolean canLinearize(Constraint c) {
        if (!(c instanceof ConstraintIntension)) {
            return false;
        }
        ConstraintIntension ic = (ConstraintIntension) c;
        boolean result = isLinearizable(ic.tree);
        if (!result && ic.tree != null) {
            // Track what patterns we're skipping
            String pattern = describePattern(ic.tree);
            skippedPatterns.merge(pattern, 1, Integer::sum);
        }
        return result;
    }

    @Override
    public boolean linearize(Constraint c, LinearizationContext ctx) {
        ConstraintIntension ic = (ConstraintIntension) c;
        return linearizeTree(ic.tree, ic, ctx);
    }

    /**
     * Get statistics about skipped patterns (for verbose logging).
     */
    public static Map<String, Integer> getSkippedPatterns() {
        return skippedPatterns;
    }

    /**
     * Describe the top-level pattern of an expression tree.
     */
    private String describePattern(XNodeParent<IVar> tree) {
        if (tree == null) return "null";
        StringBuilder sb = new StringBuilder();
        sb.append(tree.type.name());
        if (tree.sons != null && tree.sons.length > 0) {
            sb.append("(");
            for (int i = 0; i < Math.min(tree.sons.length, 3); i++) {
                if (i > 0) sb.append(",");
                XNode<IVar> son = tree.sons[i];
                if (son instanceof XNodeParent) {
                    sb.append(((XNodeParent<IVar>) son).type.name());
                } else {
                    sb.append(son.type.name());
                }
            }
            if (tree.sons.length > 3) sb.append(",...");
            sb.append(")");
        }
        return sb.toString();
    }

    /**
     * Check if an expression tree represents a linearizable constraint.
     */
    private boolean isLinearizable(XNodeParent<IVar> tree) {
        if (tree == null) return false;

        TypeExpr type = tree.type;

        // Comparison operators at the root
        if (type == TypeExpr.LE || type == TypeExpr.LT ||
            type == TypeExpr.GE || type == TypeExpr.GT || type == TypeExpr.EQ) {
            return tree.sons.length == 2 &&
                   isLinearExpression(tree.sons[0]) &&
                   isLinearExpression(tree.sons[1]);
        }

        // Implication: imp(b, constraint) where b is binary
        if (type == TypeExpr.IMP && tree.sons.length == 2) {
            if (tree.sons[0].type == TypeExpr.VAR && tree.sons[1] instanceof XNodeParent) {
                return isLinearizable((XNodeParent<IVar>) tree.sons[1]);
            }
        }

        // Disjunction of two constraints
        if (type == TypeExpr.OR && tree.sons.length == 2) {
            if (tree.sons[0] instanceof XNodeParent && tree.sons[1] instanceof XNodeParent) {
                return isLinearizable((XNodeParent<IVar>) tree.sons[0]) &&
                       isLinearizable((XNodeParent<IVar>) tree.sons[1]);
            }
        }

        // NOT of a comparison (e.g., not(le(x,y)) means gt(x,y))
        if (type == TypeExpr.NOT && tree.sons.length == 1 && tree.sons[0] instanceof XNodeParent) {
            XNodeParent<IVar> inner = (XNodeParent<IVar>) tree.sons[0];
            return isLinearizable(inner);
        }

        return false;
    }

    /**
     * Check if an expression is linear (variable, constant, or linear combination).
     */
    private boolean isLinearExpression(XNode<IVar> node) {
        if (node == null) return false;

        TypeExpr type = node.type;

        // Leaf nodes: variables and constants
        if (type == TypeExpr.VAR || type == TypeExpr.LONG || type == TypeExpr.SYMBOL) {
            return true;
        }

        if (!(node instanceof XNodeParent)) {
            return false;
        }

        XNodeParent<IVar> parent = (XNodeParent<IVar>) node;

        // Linear operations
        switch (type) {
            case ADD:
            case SUB:
                // All children must be linear
                for (XNode<IVar> child : parent.sons) {
                    if (!isLinearExpression(child)) return false;
                }
                return true;

            case NEG:
            case ABS:
                return parent.sons.length == 1 && isLinearExpression(parent.sons[0]);

            case MUL:
                // Linear if one operand is constant
                if (parent.sons.length == 2) {
                    boolean firstConst = parent.sons[0].type == TypeExpr.LONG;
                    boolean secondConst = parent.sons[1].type == TypeExpr.LONG;
                    if (firstConst) return isLinearExpression(parent.sons[1]);
                    if (secondConst) return isLinearExpression(parent.sons[0]);
                }
                return false;

            case IF:
                // if(cond, then, else) - can be linearized with big-M in some cases
                return false; // Skip for now

            default:
                return false;
        }
    }

    /**
     * Linearize the expression tree.
     */
    private boolean linearizeTree(XNodeParent<IVar> tree, ConstraintIntension ic, LinearizationContext ctx) {
        TypeExpr type = tree.type;

        // Handle comparisons
        if (type == TypeExpr.LE || type == TypeExpr.LT ||
            type == TypeExpr.GE || type == TypeExpr.GT || type == TypeExpr.EQ) {
            return linearizeComparison(tree, ic, ctx, type);
        }

        // Handle implication: imp(b, constraint)
        if (type == TypeExpr.IMP && tree.sons.length == 2) {
            return linearizeImplication(tree, ic, ctx);
        }

        // Handle disjunction: or(c1, c2)
        if (type == TypeExpr.OR && tree.sons.length == 2) {
            return linearizeDisjunction(tree, ic, ctx);
        }

        // Handle NOT
        if (type == TypeExpr.NOT && tree.sons.length == 1) {
            return linearizeNegation(tree, ic, ctx);
        }

        return false;
    }

    /**
     * Linearize a comparison: lhs OP rhs
     */
    private boolean linearizeComparison(XNodeParent<IVar> tree, ConstraintIntension ic,
                                        LinearizationContext ctx, TypeExpr op) {
        XNode<IVar> lhs = tree.sons[0];
        XNode<IVar> rhs = tree.sons[1];

        // Collect coefficients: coeff * var + constant
        Map<Variable, Double> coeffs = new HashMap<>();
        double[] constant = {0.0};

        if (!collectLinearTerms(lhs, ic.scp, coeffs, constant, 1.0)) {
            return false;
        }
        if (!collectLinearTerms(rhs, ic.scp, coeffs, constant, -1.0)) {
            return false;
        }

        // Now we have: sum(coeff[i] * x[i]) + constant OP 0
        // Rearrange to: sum(coeff[i] * x[i]) OP -constant

        Expression expr = ctx.addExpression("intension_" + ic.num);
        for (Map.Entry<Variable, Double> e : coeffs.entrySet()) {
            expr.set(ctx.getLpVar(e.getKey()), e.getValue());
        }

        double bound = -constant[0];

        switch (op) {
            case LE:
                expr.upper(bound);
                break;
            case LT:
                expr.upper(bound - 1); // Strict: x < k means x <= k-1 for integers
                break;
            case GE:
                expr.lower(bound);
                break;
            case GT:
                expr.lower(bound + 1); // Strict: x > k means x >= k+1 for integers
                break;
            case EQ:
                expr.level(bound);
                break;
            default:
                return false;
        }

        return true;
    }

    /**
     * Collect linear terms from an expression into coefficients map.
     * Returns false if the expression is not linear.
     */
    private boolean collectLinearTerms(XNode<IVar> node, Variable[] scp,
                                       Map<Variable, Double> coeffs, double[] constant, double multiplier) {
        if (node == null) return false;

        TypeExpr type = node.type;

        // Variable
        if (type == TypeExpr.VAR) {
            XNodeLeaf<IVar> leaf = (XNodeLeaf<IVar>) node;
            Variable var = findVariable(leaf.value, scp);
            if (var == null) return false;
            coeffs.merge(var, multiplier, Double::sum);
            return true;
        }

        // Constant
        if (type == TypeExpr.LONG) {
            XNodeLeaf<IVar> leaf = (XNodeLeaf<IVar>) node;
            constant[0] += multiplier * ((Number) leaf.value).doubleValue();
            return true;
        }

        if (!(node instanceof XNodeParent)) {
            return false;
        }

        XNodeParent<IVar> parent = (XNodeParent<IVar>) node;

        switch (type) {
            case ADD:
                for (XNode<IVar> child : parent.sons) {
                    if (!collectLinearTerms(child, scp, coeffs, constant, multiplier)) {
                        return false;
                    }
                }
                return true;

            case SUB:
                if (parent.sons.length == 2) {
                    if (!collectLinearTerms(parent.sons[0], scp, coeffs, constant, multiplier)) return false;
                    if (!collectLinearTerms(parent.sons[1], scp, coeffs, constant, -multiplier)) return false;
                    return true;
                }
                return false;

            case NEG:
                if (parent.sons.length == 1) {
                    return collectLinearTerms(parent.sons[0], scp, coeffs, constant, -multiplier);
                }
                return false;

            case MUL:
                if (parent.sons.length == 2) {
                    // Check if one operand is constant
                    if (parent.sons[0].type == TypeExpr.LONG) {
                        double coef = ((Number) ((XNodeLeaf<IVar>) parent.sons[0]).value).doubleValue();
                        return collectLinearTerms(parent.sons[1], scp, coeffs, constant, multiplier * coef);
                    }
                    if (parent.sons[1].type == TypeExpr.LONG) {
                        double coef = ((Number) ((XNodeLeaf<IVar>) parent.sons[1]).value).doubleValue();
                        return collectLinearTerms(parent.sons[0], scp, coeffs, constant, multiplier * coef);
                    }
                }
                return false;

            case ABS:
                // |expr| is not linear in general, skip
                return false;

            default:
                return false;
        }
    }

    /**
     * Find a variable in the scope by its IVar reference.
     */
    private Variable findVariable(Object ivar, Variable[] scp) {
        for (Variable v : scp) {
            if (v == ivar || v.equals(ivar)) {
                return v;
            }
        }
        return null;
    }

    /**
     * Linearize implication: imp(b, constraint) where b is a binary variable.
     * b=1 => constraint must hold
     * Uses big-M: when b=0, constraint is relaxed
     *
     * For b => (lhs ≤ rhs): lhs - rhs ≤ M*(1-b)
     */
    private boolean linearizeImplication(XNodeParent<IVar> tree, ConstraintIntension ic, LinearizationContext ctx) {
        XNode<IVar> condition = tree.sons[0];
        XNode<IVar> consequent = tree.sons[1];

        // Condition must be a binary variable
        if (condition.type != TypeExpr.VAR) {
            return false;
        }

        Variable bVar = findVariable(((XNodeLeaf<IVar>) condition).value, ic.scp);
        if (bVar == null || !ctx.isBinary01Domain(bVar.dom)) {
            return false;
        }

        // Consequent must be a comparison
        if (!(consequent instanceof XNodeParent)) {
            return false;
        }

        XNodeParent<IVar> cmpTree = (XNodeParent<IVar>) consequent;
        TypeExpr op = cmpTree.type;

        if (op != TypeExpr.LE && op != TypeExpr.LT && op != TypeExpr.GE && op != TypeExpr.GT && op != TypeExpr.EQ) {
            return false;
        }

        // Collect linear terms from comparison
        Map<Variable, Double> coeffs = new HashMap<>();
        double[] constant = {0.0};

        if (!collectLinearTerms(cmpTree.sons[0], ic.scp, coeffs, constant, 1.0)) {
            return false;
        }
        if (!collectLinearTerms(cmpTree.sons[1], ic.scp, coeffs, constant, -1.0)) {
            return false;
        }

        // Compute big-M based on variable bounds
        double M = computeBigM(coeffs, ic.scp);
        if (M <= 0) M = 10000; // Fallback

        // For b => (sum ≤ -constant): sum + M*b ≤ -constant + M
        // When b=1: sum ≤ -constant (constraint holds)
        // When b=0: sum ≤ -constant + M (relaxed)

        Expression expr = ctx.addExpression("intension_imp_" + ic.num);
        for (Map.Entry<Variable, Double> e : coeffs.entrySet()) {
            expr.set(ctx.getLpVar(e.getKey()), e.getValue());
        }

        double bound = -constant[0];

        switch (op) {
            case LE:
            case LT:
                // b => (lhs ≤ rhs): lhs - rhs - M*(1-b) ≤ 0
                // lhs - rhs + M*b ≤ M
                expr.set(ctx.getLpVar(bVar), -M);
                expr.upper(bound);
                break;
            case GE:
            case GT:
                // b => (lhs ≥ rhs): lhs - rhs + M*(1-b) ≥ 0
                // lhs - rhs - M*b ≥ -M
                expr.set(ctx.getLpVar(bVar), M);
                expr.lower(bound);
                break;
            case EQ:
                // b => (lhs = rhs): need both directions, complex
                return false;
            default:
                return false;
        }

        return true;
    }

    /**
     * Linearize disjunction: or(c1, c2)
     * At least one of c1 or c2 must hold.
     * Uses auxiliary binary: b=1 means c1 holds, b=0 means c2 holds
     */
    private boolean linearizeDisjunction(XNodeParent<IVar> tree, ConstraintIntension ic, LinearizationContext ctx) {
        XNode<IVar> c1 = tree.sons[0];
        XNode<IVar> c2 = tree.sons[1];

        if (!(c1 instanceof XNodeParent) || !(c2 instanceof XNodeParent)) {
            return false;
        }

        XNodeParent<IVar> cmp1 = (XNodeParent<IVar>) c1;
        XNodeParent<IVar> cmp2 = (XNodeParent<IVar>) c2;

        // Both must be LE comparisons (common in scheduling)
        if (cmp1.type != TypeExpr.LE || cmp2.type != TypeExpr.LE) {
            return false;
        }

        // Collect terms for both comparisons
        Map<Variable, Double> coeffs1 = new HashMap<>();
        double[] constant1 = {0.0};
        Map<Variable, Double> coeffs2 = new HashMap<>();
        double[] constant2 = {0.0};

        if (!collectLinearTerms(cmp1.sons[0], ic.scp, coeffs1, constant1, 1.0)) return false;
        if (!collectLinearTerms(cmp1.sons[1], ic.scp, coeffs1, constant1, -1.0)) return false;
        if (!collectLinearTerms(cmp2.sons[0], ic.scp, coeffs2, constant2, 1.0)) return false;
        if (!collectLinearTerms(cmp2.sons[1], ic.scp, coeffs2, constant2, -1.0)) return false;

        double M1 = computeBigM(coeffs1, ic.scp);
        double M2 = computeBigM(coeffs2, ic.scp);
        if (M1 <= 0) M1 = 10000;
        if (M2 <= 0) M2 = 10000;

        // Create auxiliary binary b
        org.ojalgo.optimisation.Variable b = org.ojalgo.optimisation.Variable
            .make("intension_or_" + ic.num + "_b").lower(0).upper(1);
        ctx.addVariable(b);

        // c1: sum1 ≤ -const1 when b=1 => sum1 + M1*(1-b) ≤ -const1 + M1
        // => sum1 - M1*b ≤ -const1
        Expression expr1 = ctx.addExpression("intension_or1_" + ic.num);
        for (Map.Entry<Variable, Double> e : coeffs1.entrySet()) {
            expr1.set(ctx.getLpVar(e.getKey()), e.getValue());
        }
        expr1.set(b, M1);
        expr1.upper(-constant1[0] + M1);

        // c2: sum2 ≤ -const2 when b=0 => sum2 + M2*b ≤ -const2 + M2
        Expression expr2 = ctx.addExpression("intension_or2_" + ic.num);
        for (Map.Entry<Variable, Double> e : coeffs2.entrySet()) {
            expr2.set(ctx.getLpVar(e.getKey()), e.getValue());
        }
        expr2.set(b, -M2);
        expr2.upper(-constant2[0]);

        return true;
    }

    /**
     * Compute a big-M value based on variable bounds in a linear expression.
     */
    private double computeBigM(Map<Variable, Double> coeffs, Variable[] scp) {
        double maxVal = 0;
        double minVal = 0;

        for (Map.Entry<Variable, Double> e : coeffs.entrySet()) {
            Variable v = e.getKey();
            double c = e.getValue();
            double lb = v.dom.firstValue();
            double ub = v.dom.lastValue();

            if (c > 0) {
                maxVal += c * ub;
                minVal += c * lb;
            } else {
                maxVal += c * lb;
                minVal += c * ub;
            }
        }

        return Math.max(Math.abs(maxVal), Math.abs(minVal)) + 1;
    }

    /**
     * Linearize negation: not(comparison)
     * not(le(x,y)) = gt(x,y) = ge(x, y+1) for integers
     */
    private boolean linearizeNegation(XNodeParent<IVar> tree, ConstraintIntension ic, LinearizationContext ctx) {
        XNodeParent<IVar> inner = (XNodeParent<IVar>) tree.sons[0];
        TypeExpr innerType = inner.type;

        // Flip the comparison
        TypeExpr flipped;
        switch (innerType) {
            case LE: flipped = TypeExpr.GT; break;
            case LT: flipped = TypeExpr.GE; break;
            case GE: flipped = TypeExpr.LT; break;
            case GT: flipped = TypeExpr.LE; break;
            case EQ: return false; // NE is disjunctive, skip
            default: return false;
        }

        return linearizeComparison(inner, ic, ctx, flipped);
    }
}
