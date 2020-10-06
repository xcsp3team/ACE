/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Table;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

// java abscon.Resolution problems.generators.NurseRosteringReader ~/instances/nurseRostering/24Instances/10 -r_n=20 => bound=38152
public class NurseRostering implements ProblemAPI {
	int nDays;
	Shift[] shifts;
	Staff[] staffs;
	Cover[][] covers;

	class Shift {
		String id = "_off";
		int length;
		String[] forbiddenFollowingShifts;
	}

	class Request {
		int day;
		String shift;
		int weight;
	}

	class Staff {
		String id;
		int maxShifts[], minTotalMinutes, maxTotalMinutes, minConsecutiveShifts, maxConsecutiveShifts, minConsecutiveDaysOff, maxWeekends, daysOff[];
		Request[] onRequests, offRequests;
	}

	class Cover {
		int requirement, weightIfUnder, weightIfOver;

		int costFor(int i) {
			return i <= requirement ? (requirement - i) * weightIfUnder : (i - requirement) * weightIfOver;
		}
	}

	private Request onRequest(int person, int day) {
		return firstFrom(staffs[person].onRequests, request -> request.day == day);
	}

	private Request offRequest(int person, int day) {
		return firstFrom(staffs[person].offRequests, request -> request.day == day);
	}

	// private int weightOn(Request[] requests, int day) {
	// Request request = firstFrom(requests, req -> req.day == day);
	// return request == null ? -1 : request.weight;
	// }

	private int shiftPos(String s) {
		return firstFrom(range(shifts.length), i -> shifts[i].id.equals(s));
	}

	private int[] costsFor(int day, int shift) {
		int[] t = new int[staffs.length + 1];
		if (shift != shifts.length - 1) // if not '_off'
			for (int i = 0; i < t.length; i++)
				t[i] = covers[day][shift].costFor(i);
		return t;
	}

	private Automaton automatonMinConsecutive(int nShifts, int k, boolean forShifts) {
		Range rangeOff = range(nShifts - 1, nShifts); // a range with only one value (off)
		Range rangeNotOff = range(nShifts - 1); // a range with all other values
		Range r1 = forShifts ? rangeOff : rangeNotOff, r2 = forShifts ? rangeNotOff : rangeOff;
		Transitions transitions = transitions();
		transitions.add("q0", r1, "q1").add("q0", r2, "q" + (k + 1)).add("q1", r1, "q" + (k + 1));
		for (int i = 1; i <= k; i++)
			transitions.add("q" + i, r2, "q" + (i + 1));
		transitions.add("q" + (k + 1), range(nShifts), "q" + (k + 1));
		return automaton("q0", transitions, finalState("q" + (k + 1)));
	}

	private Table rotation() {
		Table table = table(NEGATIVE);
		for (Shift s1 : shifts)
			if (s1.forbiddenFollowingShifts != null)
				for (String s2 : s1.forbiddenFollowingShifts)
					table.add(shiftPos(s1.id), shiftPos(s2));
		return table;
	}

	private void buildDummyShift() {
		shifts = addObject(shifts, new Shift()); // we add first a dummy off shift
		for (Staff staff : staffs)
			staff.maxShifts = addInt(staff.maxShifts, nDays); // we add no limit (nDays) for the new off shift
	}

	@Override
	public void model() {
		buildDummyShift();
		// shifts = addObject(shifts, new Shift()); // we add first a dummy off shift
		int nWeeks = nDays / 7, nShifts = shifts.length, nStaffs = staffs.length;
		int off = nShifts - 1; // value for _off

		Var[][] x = array("x", size(nDays, nStaffs), dom(range(nShifts)), "x[d][p] is the shift at day d for person p (value " + off + " denotes off)");
		Var[][] nd = array("nd", size(nStaffs, nShifts), (p, s) -> dom(range(staffs[p].maxShifts[s] + 1)),
				"nd[p][s] is the number of days such that person p works with shift s");
		Var[][] np = array("np", size(nDays, nShifts), dom(range(nStaffs + 1)), "np[d][s] is the number of persons working on day d with shift s");
		Var[][] wk = array("wk", size(nStaffs, nWeeks), dom(0, 1), "wk[p][w] is 1 iff the week-end w is worked by person p");

		Var[][] cn = array("cn", size(nStaffs, nDays), (p, d) -> onRequest(p, d) != null ? dom(0, onRequest(p, d).weight) : null,
				"cn[p][d] is the cost of not satisfying the on-request (if it exists) of person p on day d");
		Var[][] cf = array("cf", size(nStaffs, nDays), (p, d) -> offRequest(p, d) != null ? dom(0, offRequest(p, d).weight) : null,
				"cf[p][d] is the cost of not satisfying the off-request (if it exists) of person p on day d");
		Var[][] cc = array("cc", size(nDays, nShifts), (d, s) -> dom(costsFor(d, s)), "cc[d][s] is the cost of not satisfying cover for shift s on day d");

		instantiation(select(x, (d, p) -> contains(staffs[p].daysOff, d)), takingValue(off)).note("days off for staff");

		forall(range(nStaffs).range(nShifts), (p, s) -> exactly(columnOf(x, p), takingValue(s), nd[p][s])).note("computing number of days");
		forall(range(nDays).range(nShifts), (d, s) -> exactly(x[d], takingValue(s), np[d][s])).note("computing number of persons");

		forall(range(nStaffs).range(nWeeks), (p, w) -> {
			implication(ne(x[w * 7 + 5][p], off), wk[p][w]);
			implication(ne(x[w * 7 + 6][p], off), wk[p][w]);
		}).note("computing worked week-ends");

		Table table = rotation();
		if (table.size() > 0)
			forall(range(nStaffs), p -> slide(columnOf(x, p), range(nDays - 1), i -> extension(vars(x[i][p], x[i + 1][p]), table))).note("rotation shifts");

		forall(range(nStaffs), p -> sum(wk[p], LE, staffs[p].maxWeekends)).note("maximum number of worked week-ends");

		int[] lengths = valuesFrom(shifts, sh -> sh.length);
		forall(range(nStaffs), p -> sum(nd[p], weightedBy(lengths), IN, rangeClosed(staffs[p].minTotalMinutes, staffs[p].maxTotalMinutes)))
				.note("minimum and maximum number of total worked minutes");

		forall(range(nStaffs), p -> {
			int k = staffs[p].maxConsecutiveShifts;
			forall(range(nDays - k), i -> atLeast1(select(columnOf(x, p), range(i, i + k + 1)), takingValue(off)));
		}).note("maximum consecutive worked shifts");

		forall(range(nStaffs), p -> {
			int k = staffs[p].minConsecutiveShifts;
			forall(range(nDays - k), i -> regular(select(columnOf(x, p), range(i, i + k + 1)), automatonMinConsecutive(nShifts, k, true)));
		}).note("minimum consecutive worked shifts");

		forall(range(nStaffs), p -> {
			int k = staffs[p].minConsecutiveShifts;
			if (k > 1) {
				forall(range(1, k), i -> implication(ne(x[0][p], off), ne(x[i][p], off)));
				forall(range(1, k), i -> implication(ne(x[nDays - 1][p], off), ne(x[nDays - 1 - i][p], off)));
			}
		}).note("managing off days on schedule ends");

		forall(range(nStaffs), p -> {
			int k = staffs[p].minConsecutiveDaysOff;
			forall(range(nDays - k), i -> regular(select(columnOf(x, p), range(i, i + k + 1)), automatonMinConsecutive(nShifts, k, false)));
		}).note("minimum consecutive days off");

		forall(range(nStaffs).range(nDays), (p, d) -> {
			if (onRequest(p, d) != null)
				equivalence(eq(x[d][p], shiftPos(onRequest(p, d).shift)), eq(cn[p][d], 0));
		}).note("cost of not satisfying on requests");

		forall(range(nStaffs).range(nDays), (p, d) -> {
			if (offRequest(p, d) != null)
				equivalence(eq(x[d][p], shiftPos(offRequest(p, d).shift)), ne(cf[p][d], 0));
		}).note("cost of not satisfying off requests");

		// System.out.println("Tuples= " + Kit.join(number(costsFor(0, 0))));
		forall(range(nDays).range(nShifts), (d, s) -> extension(vars(np[d][s], cc[d][s]), indexing(costsFor(d, s)))).note("cost of under or over covering");

		Var[] vars = vars(cn, cf, cc);
		minimize(SUM, vars);
	}
}

// return staffs[person].onRequests == null ? null : Stream.of(staffs[person].onRequests).filter(r -> r.day == day).findFirst().orElse(null);

// Map<String, Integer> mapShift = IntStream.range(0, nShifts).boxed().collect(Collectors.toMap(i -> shifts[i].id, i -> i));
// map instead of calling shiftPos

// private IntStream costsFor(int d, int s) {
// if (s == shifts.length - 1)
// return IntStream.generate(() -> 0).limit(staffs.length + 1); // repeat(0, staffs.length + 1); // because dummy off shift
// return IntStream.range(0, staffs.length + 1).map(i -> i <= covers[d][s].requirement ? (covers[d][s].requirement - i) *
// covers[d][s].weightIfUnder
// : (i - covers[d][s].requirement) * covers[d][s].weightIfOver);
// }

// int[] t1 = IntStream.range(0, nStaffs).flatMap(p -> IntStream.range(0, nDays).filter(d -> onRequestFor(p, d) != null).map(d -> p * nDays +
// d))
// .toArray();
// ABOVE, if we van deal with undefined variables

// Var[][] cn = array("cn", size(nStaffs, nDays), (p, d) -> onRequestFor(p, d) != null ? dom(0, onRequestFor(p, d).weight) : null,
// "cn[p][d] is the cost of not satisfying on request for person p on day d");
// Var[][] cf = array("cf", size(nStaffs, nDays), (p, d) -> offRequestFor(p, d) != null ? dom(0, offRequestFor(p, d).weight) : null,
// "cf[p][d] is the cost of not satisfying off request for person p on day d");
