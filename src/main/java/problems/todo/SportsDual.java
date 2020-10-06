package problems.todo;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class SportsDual implements ProblemAPI {
	int nTeams; // must be even

	@Override
	public void model() {
		int nWeeks = nTeams - 1, nPeriods = nTeams / 2;

		if (modelVariant("m1")) {
			Var[][] o = array("o", size(nWeeks, nTeams), dom(range(nTeams)), "o[w][t] gives at week w the opponent of team t");
			Var[][] p = array("p", size(nWeeks, nTeams), dom(range(nPeriods)), "p[w][t] gives the period at week w of team t");
			Var[] d = array("d", size(nTeams), dom(range(nPeriods)), "d[t] gives the dummy period of team t");

			forall(range(nWeeks), w -> allDifferent(o[w])).note("Each week, all teams have a different opponent");
			forall(range(nWeeks).range(nTeams), (w, t) -> different(o[w][t], t)).note("Each week, a team can't play against itself");
			forall(range(nWeeks).range(nTeams).range(nTeams), (w, t1, t2) -> {
				if (t1 < t2)
					equivalence(eq(o[w][t1], t2), eq(o[w][t2], t1), eq(p[w][t1], p[w][t2]));
			}).note("j plays k <=> k plays j <=> j and k play on the same period");
			forall(range(nTeams), t -> allDifferent(columnOf(o, t))).note("Each team has a different opponent every week");
			forall(range(nTeams), t -> cardinality(vars(columnOf(p, t), d[t]), vals(range(nPeriods)), occursEachExactly(2)));
			forall(range(nTeams), t -> equal(p[0][t], t / 2)).note("Symmetry breaking: assign opponents and periods for week 0");
			forall(range(0, nTeams, 2), t -> intension(lt(p[1][t], p[1][t + 1]))).note("Symmetry breaking: order periods on week 1");
		}
		if (modelVariant("m2")) {
			Var[][] w = array("w", size(nTeams, nTeams), dom(range(nWeeks + 1)), "w[t1][t2] gives the week of the match between t1 and t2");

			forall(range(nTeams).range(nTeams), (i, j) -> {
				if (i < j)
					different(w[i][j], nWeeks);
				else
					equal(w[i][j], nWeeks);
			}).note("Exactly nPeriods matches each week");
			cardinality(select(w, (i, j) -> i < j), vals(range(nWeeks)), occursEachExactly(nPeriods));
			forall(range(nTeams), t -> allDifferent(vars(select(w, (i, j) -> i < t && j == t), select(w, (i, j) -> i == t && j > t))))
					.note("A team cannot play twice in the same week");
			forall(range(1, nTeams), t -> equal(w[0][t], t - 1)).note("Symmetry breaking: team 0 plays team i on week i-1");
			forall(range(2, nTeams, 2), t -> equal(w[t][t + 1], 0)).note("Symmetry breaking: matches are assigned for week 0");
		}
	}

	@Override
	public void prettyDisplay(String[] values) {
		if (modelVariant("m1"))
			return;
		int nWeeks = nTeams - 1, nPeriods = nTeams / 2;
		int[][][] matches = new int[nPeriods][nWeeks][];
		for (int i = 0; i < nPeriods; i++)
			for (int j = 0; j < nWeeks; j++)
				matches[i][j] = new int[] { -1, -1 };
		for (int i = 0; i < nTeams; i++)
			for (int j = i + 1; j < nTeams; j++) {
				int matchWeek = Integer.parseInt(values[i * nTeams + j]);
				for (int k = 0; k < nPeriods; k++)
					if (matches[k][matchWeek][0] == -1) {
						matches[k][matchWeek][0] = i;
						matches[k][matchWeek][1] = j;
						break;
					}
			}
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < nPeriods; i++) {
			for (int j = 0; j < nWeeks; j++)
				sb.append(matches[i][j][0] + "vs" + matches[i][j][1] + "\t");
			sb.append("\n");
		}
		String result = sb.toString();

		try (BufferedWriter output = new BufferedWriter(new FileWriter("SportsDual.txt"))) {
			output.write(result);
			output.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
