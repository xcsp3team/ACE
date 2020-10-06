/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import static java.lang.Integer.parseInt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.NurseRostering;
import utility.Kit;

public class NurseRosteringReader extends NurseRostering implements ReaderTxt {

	private String skipComments(String line) {
		while (line.length() == 0 || line.startsWith("#"))
			line = nextLine().trim();
		return line;
	}

	private class LocalStaff {
		private String id;
		private int[] maxShifts;
		private int minTotalMinutes, maxTotalMinutes;
		private int minConsecutiveShifts, maxConsecutiveShifts;
		private int minConsecutiveDaysOff;
		private int maxWeekends;
		private int[] daysOff;
		private List<Object> onRequests = new ArrayList<>();
		private List<Object> offRequests = new ArrayList<>();

		private LocalStaff(String[] tokens) {
			this.id = tokens[0];
			this.maxShifts = Stream.of(tokens[1].split("\\|")).mapToInt(s -> parseInt(s.substring(s.indexOf("=") + 1))).toArray();
			this.minTotalMinutes = parseInt(tokens[3]);
			this.maxTotalMinutes = parseInt(tokens[2]);
			this.minConsecutiveShifts = parseInt(tokens[5]);
			this.maxConsecutiveShifts = parseInt(tokens[4]);
			this.minConsecutiveDaysOff = parseInt(tokens[6]);
			this.maxWeekends = parseInt(tokens[7]);
		}
	}

	void data() {
		BiConsumer<String, Consumer<String[]>> c = (s, r) -> {
			String line = skipComments(nextLine().trim());
			Kit.control(line.equals(s));
			line = skipComments(nextLine().trim());
			while (line != null && line.length() != 0) {
				String[] tokens = line.split(",");
				r.accept(tokens);
				if (!hasNextLine())
					break;
				line = nextLine();
				if (line != null)
					line = line.trim();
			}
		};

		String line = skipComments(nextLine().trim());
		Kit.control(line.equals("SECTION_HORIZON"));
		int nDays = parseInt(skipComments(nextLine().trim()));

		// Shifts
		Map<String, Integer> mapShift = new HashMap<>();
		List<Object> listShifts = new ArrayList<>();
		c.accept("SECTION_SHIFTS", toks -> {
			Object shift = buildInternClassObject("Shift", toks[0], parseInt(toks[1]),
					toks.length == 2 ? null : Stream.of(toks[2].split("\\|")).toArray(String[]::new));
			listShifts.add(shift);
			mapShift.put(toks[0], mapShift.size());
		});
		// Map<String, Integer> mapShift = IntStream.range(0, shifts.length).boxed().collect(Collectors.toMap(i -> shifts[i].id, i -> i));

		// Staffs
		List<LocalStaff> localStaffs = new ArrayList<>();
		c.accept("SECTION_STAFF", tokens -> localStaffs.add(new LocalStaff(tokens)));
		Map<String, Integer> mapStaff = IntStream.range(0, localStaffs.size()).boxed().collect(Collectors.toMap(i -> localStaffs.get(i).id, i -> i));
		c.accept("SECTION_DAYS_OFF", tokens -> {
			int staff = mapStaff.get(tokens[0]);
			localStaffs.get(staff).daysOff = IntStream.range(1, tokens.length).map(j -> parseInt(tokens[j])).toArray();
		});
		c.accept("SECTION_SHIFT_ON_REQUESTS", toks -> {
			int staff = mapStaff.get(toks[0]);
			localStaffs.get(staff).onRequests.add(buildInternClassObject("Request", parseInt(toks[1]), toks[2], parseInt(toks[3])));
		});
		c.accept("SECTION_SHIFT_OFF_REQUESTS", tokens -> {
			int staff = mapStaff.get(tokens[0]);
			localStaffs.get(staff).offRequests.add(buildInternClassObject("Request", parseInt(tokens[1]), tokens[2], parseInt(tokens[3])));
		});
		Stream<Object> staffs = localStaffs.stream()
				.map(s -> buildInternClassObject("Staff", s.id, s.maxShifts, s.minTotalMinutes, s.maxTotalMinutes, s.minConsecutiveShifts,
						s.maxConsecutiveShifts, s.minConsecutiveDaysOff, s.maxWeekends, s.daysOff, Utilities.convert(s.onRequests),
						Utilities.convert(s.offRequests)));

		Object[][] covers = new Object[nDays][listShifts.size()];
		c.accept("SECTION_COVER", tokens -> {
			int day = parseInt(tokens[0]);
			int shift = mapShift.get(tokens[1]);
			covers[day][shift] = buildInternClassObject("Cover", parseInt(tokens[2]), parseInt(tokens[3]), parseInt(tokens[4]));
		});
		setDataValues(nDays, listShifts, staffs, Utilities.convert(covers));
	}

}
