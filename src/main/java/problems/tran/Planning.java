/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.tran;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Scanner;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;
import variables.Variable;

// This problem involves determining if there exists a plan for the specified file
public class Planning implements ProblemAPI {

	class Action {
		String name;
		int duration;
		int[] precs, adds, dels;

		Action() { // necessary for being able to load data
		}

		Action(String name, int duration, int[] precs, int[] adds, int[] dels) {
			this.name = name;
			this.duration = duration;
			this.precs = Kit.sort(precs);
			this.adds = Kit.sort(adds);
			this.dels = Kit.sort(dels);
		}

		@Override
		public String toString() {
			return name + " " + duration + " precs = (" + Kit.join(precs) + ") adds = (" + Kit.join(adds) + ") dels = (" + Kit.join(dels) + ")";
		}
	}

	String[] fluents;
	Action[] actions;
	int nActions;
	int timeLimit = 30;
	int nMaxPrecs, nMaxSupps, nMaxDels;
	int[][][] possibleSupporters, deleters;

	void data() {
		String fileName = imp().askString("instance filename");
		try (Scanner scanner = new Scanner(new File(fileName))) {
			while (scanner.hasNext("#.*"))
				scanner.nextLine();
			int nbFluents = scanner.nextInt();
			fluents = IntStream.range(0, nbFluents).mapToObj(i -> scanner.next()).toArray(String[]::new);
			while (scanner.hasNext("#.*"))
				scanner.nextLine();
			nActions = scanner.nextInt();
			actions = new Action[nActions];
			for (int i = 0; i < actions.length; i++) {
				String name = scanner.next();
				int duration = scanner.nextInt();
				int[] precs = IntStream.range(0, scanner.nextInt()).map(j -> scanner.nextInt()).toArray();
				int[] adds = IntStream.range(0, scanner.nextInt()).map(j -> scanner.nextInt()).toArray();
				int[] dels = IntStream.range(0, scanner.nextInt()).map(j -> scanner.nextInt()).toArray();
				dels = Arrays.stream(dels).filter(d -> !Kit.isPresent(d, adds)).toArray(); // remove Commun Fluents (dels, adds)
				actions[i] = new Action(name, duration, precs, adds, dels);
				// System.out.println("action " + i + " " + actions[i]);
			}
		} catch (IOException e) {
			Kit.exit("Erreur ouverture fichier", e);
		}
		nMaxPrecs = Stream.of(actions).mapToInt(a -> a.precs.length).max().orElse(-1);
		int[][][] t = new int[actions.length][][];
		for (int i = 0; i < t.length; i++) {
			t[i] = new int[actions[i].precs.length][];
			for (int j = 0; j < t[i].length; j++) {
				t[i][j] = supportersOfExcept(actions[i].precs[j], i);
				nMaxSupps = Math.max(nMaxSupps, t[i][j].length);
			}
		}
		possibleSupporters = t;
		t = new int[actions.length][][];
		for (int i = 0; i < t.length; i++) {
			t[i] = new int[actions[i].precs.length][];
			for (int j = 0; j < t[i].length; j++) {
				t[i][j] = deletersOf(actions[i].precs[j]);
				nMaxDels = Math.max(nMaxDels, t[i][j].length);
			}
		}
		deleters = t;
	}

	int[] deletersOf(int prec) {
		return IntStream.range(0, actions.length).filter(i -> Arrays.binarySearch(actions[i].dels, prec) >= 0).toArray();
	}

	int[] supportersOfExcept(int prec, int action) {
		return IntStream.range(0, actions.length).filter(i -> i != action && Arrays.binarySearch(actions[i].adds, prec) >= 0).toArray();
	}

	XNodeParent<IVar> buildPreconditionPredicate(IVar x, IVar y, IVar z) {
		return or(eq(x, -1), ne(y, ((Variable) z).num), and(ne(z, -1), le(add(z, actions[((Variable) z).num].duration), x)));
	}

	XNodeParent<IVar> buildCausalPredicate(IVar x, IVar y, IVar z, IVar w) {
		return or(eq(x, -1), ne(y, ((Variable) z).num),
				and(ne(z, -1), or(eq(w, -1), lt(add(w, actions[((Variable) w).num].duration), z), lt(add(x, actions[((Variable) x).num].duration), w))));
	}

	@Override
	public void model() {
		Var[] a = array("a", size(actions.length), i -> i == 0 ? dom(0) : i == 1 ? dom(range(timeLimit + 1)) : dom(range(-1, timeLimit + 1)));
		// start at i=0, and at i=1
		Var[][] x = array("x", size(actions.length, nMaxPrecs), (i, j) -> j < actions[i].precs.length ? dom(supportersOfExcept(actions[i].precs[j], i)) : null);

		forall(range(2, nActions), i -> intension(le(sub(a[i], a[1]), actions[i].duration)));
		forall(range(nActions).range(nMaxPrecs).range(nMaxSupps), (i, j, k) -> {
			if (j < actions[i].precs.length && k < possibleSupporters[i][j].length)
				intension(buildPreconditionPredicate(a[i], x[i][j], a[possibleSupporters[i][j][k]]));
		});
		forall(range(nActions).range(nMaxPrecs).range(nMaxSupps).range(nMaxDels), (i, j, k, l) -> {
			if (j < actions[i].precs.length && k < possibleSupporters[i][j].length && l < deleters[i][j].length && i != deleters[i][j][l])
				intension(buildCausalPredicate(a[i], x[i][j], a[possibleSupporters[i][j][k]], a[deleters[i][j][l]]));
		});
	}
}

// class PreconditionConstraint extends CtrAdhoc {
// int presumedActionForPrecondition;
// int d;
//
// PreconditionConstraint(Problem problem, Var[] variables) {
// super(problem, variables);
// presumedActionForPrecondition = variables[2].id;
// d = actions[presumedActionForPrecondition].duration;
// }
//
// @Override
// public final boolean checkVals(int[] vals) {
// return vals[0] == -1 || vals[1] != presumedActionForPrecondition || (vals[2] != -1 && vals[2] + d <= vals[0]);
// }
// }
//
// private class CausalConstraint extends CtrAdhoc {
// private int action;
// private int presumedAdder;
// private int presumedDeleter;
// int d1, d2;
//
// private CausalConstraint(Problem problem, Var[] variables) {
// super(problem, variables);
// action = variables[0].id;
// presumedAdder = variables[2].id;
// presumedDeleter = variables[3].id;
// d1 = actions[presumedDeleter].duration;
// d2 = actions[action].duration;
// }
//
// @Override
// public final boolean checkVals(int[] vals) {
// return vals[0] == -1 || vals[1] != presumedAdder || (vals[2] != -1 && (vals[3] == -1 || vals[3] + d1 < vals[2] || vals[0] + d2 <
// vals[3]));
// }
// }
//
// private void addCausalConstraints() {
// for (int i = 0; i < actions.length; i++)
// for (int j = 0; j < actions[i].precs.length; j++)
// for (int k = 0; k < possibleSupporters[i][j].length; k++)
// for (int l = 0; l < deleters[i][j].length; l++)
// if (i != deleters[i][j][l])
// addCtr(new CausalConstraint(this, vars(a[i], x[i][j], a[possibleSupporters[i][j][k]], a[deleters[i][j][l]])));
// }
