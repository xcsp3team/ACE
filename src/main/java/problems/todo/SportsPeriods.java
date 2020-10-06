package problems.todo;

import java.util.StringTokenizer;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import problems.ReaderFile.ReaderTxt;
import utility.Kit;

public class SportsPeriods implements ProblemAPI, ReaderTxt {

	int nTeams;
	int[][][] originalMatches;

	void data() {
		// you must Enter the name of a file containing a solution of the sports scheduling problem without the period constraints (eg. use
		// SportsDual)
		int nWeeks = -1;
		int currentPeriod = 0;
		while (hasNextLine()) {
			StringTokenizer st = new StringTokenizer(nextLine(), Constants.WHITE_SPACE);
			if (nWeeks == -1) {
				nWeeks = st.countTokens();
				Kit.control(nWeeks % 2 == 1);
				nTeams = nWeeks + 1;
				originalMatches = new int[nTeams / 2][nWeeks][2];
			} else
				Kit.control(nWeeks == st.countTokens());
			for (int i = 0; i < nWeeks; i++) {
				StringTokenizer st2 = new StringTokenizer(st.nextToken(), "vs");
				Kit.control(st2.countTokens() == 2);
				originalMatches[currentPeriod][i][0] = Integer.parseInt(st2.nextToken());
				originalMatches[currentPeriod][i][1] = Integer.parseInt(st2.nextToken());
			}
			currentPeriod++;
		}
		Kit.control(currentPeriod == nTeams / 2);
	}

	private int matchNumberFor(int nPossibleMatches, int idTeam1, int idTeam2) {
		return nPossibleMatches - ((nTeams - idTeam1) * (nTeams - idTeam1 - 1)) / 2 + (idTeam2 - idTeam1 - 1);
	}

	@Override
	public void model() {
		int nWeeks = nTeams - 1, nPeriods = nTeams / 2, nPossibleMatches = (nTeams * (nTeams - 1)) / 2;

		Var[][] h = array("h", size(nPeriods, nWeeks), dom(range(nTeams))); // number of the opponent
		Var[][] a = array("a", size(nPeriods, nWeeks), dom(range(nTeams))); // number of the opponent
		Var[][] m = array("m", size(nPeriods, nWeeks), dom(range(nPossibleMatches)));

		// Linking variables through ternary table constraints
		Table matchNums = table().addFrom(range(nTeams).range(nTeams), (i, j) -> i < j ? tuple(i, j, matchNumberFor(nPossibleMatches, i, j)) : null);
		forall(range(nPeriods).range(nWeeks), (p, w) -> extension(vars(h[p][w], a[p][w], m[p][w]), matchNums))
				.note("Linking variables through ternary table constraints");

		// Each week, all matches are different and included in a restricted scope given in the input file.
		int[][] allowedMatches = new int[nPeriods][1];
		for (int i = 0; i < nWeeks; i++) {
			for (int j = 0; j < nPeriods; j++)
				allowedMatches[j][0] = matchNumberFor(nPossibleMatches, originalMatches[j][i][0], originalMatches[j][i][1]);
			for (int j = 0; j < nPeriods; j++)
				extension(new Var[] { m[j][i] }, allowedMatches);
			allDifferent(columnOf(m, i));
		}

		// Each team plays at most two times in each period
		// if (!dummyWeek)
		forall(range(nPeriods), p -> cardinality(vars(h[p], a[p]), vals(range(nTeams)), occursEachBetween(1, 2)))
				.note("Each team plays at most two times in each period"); // TODO a tag for negation of dummyWeek

		// Breaking symmetries : the first week is set : 0 vs 1, 2 vs 3, 4 vs 5, etc.
		// for (int i = 1; i < nbPeriods; i++)
		// addConstraint(Expr.eq(matchs[i][0], getMatchNumberFor(2 * i, 2 * i + 1)));
		// Breaking symmetries : the match "0 versus T" (with T > 0) appears at period (T-1)%nbPeriods and week T-1
		// for (int i = 1; i < nbTeams; i++)
		// addConstraintIntension(Expr.eq(matchs[(i - 1) % nbPeriods][i - 1], getMatchNumberFor(0, i)));
		// Breaking symmetries : the match "0 versus T" (with T > 0) appears at week T-1
		// for (int i = 1; i < nbWeeks; i++)
		// addConstraintExactlyOne(Variable.columnOf(matchs, i), getMatchNumberFor(0, (i + 1)));

		// Handling dummy variables and constraints
		block(() -> {
			Var[] hd = array("hd", size(nPeriods), dom(range(nTeams)), "hd[p] is the number of the home opponent for the dummy match of the period");
			Var[] ad = array("ad", size(nPeriods), dom(range(nTeams)), "ad[p] is the number of the away opponent for the dummy match of the period");

			forall(range(nPeriods), p -> cardinality(vars(h[p], hd[p], ad[p], a[p]), vals(range(nTeams)), occursEachExactly(2)))
					.note("Each team plays two times in each period");
			allDifferent(vars(hd, ad));
			forall(range(nPeriods), p -> intension(lt(hd[p], ad[p])));
			// equal(hd[nPeriods - 1], 0); equal(ad[nPeriods - 1], nTeams - 1);
		}).tag("dummyWeek");
	}

	// @Override
	// public void prettyDisplay() {
	// for (int i = 0; i < nPeriods; i++) {
	// for (int j = 0; j < nWeeks; j++)
	// Kit.log.config((j == 0 ? "\n" : "") + ((Variable) h[i][j]).dom.uniqueValue() + "vs" + ((Variable) a[i][j]).dom.uniqueValue() + "\t");
	// // if (dummyWeek)
	// // Kit.pr(hd[i].dom.uniqueValue() + "vs" + ad[i].dom.uniqueValue());
	// }

	// }
}
