/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Scanner;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

public interface ReaderFile extends ProblemAPI {

	default Scanner scanner() {
		return imp().fileScanner();
	}

	default boolean hasNextInt() {
		return imp().fileScanner().hasNextInt();
	}

	default boolean hasNextLine() {
		return imp().fileScanner().hasNextLine();
	}

	default String next() {
		return imp().fileScanner().next();
	}

	default String nextLine() {
		return imp().fileScanner().nextLine();
	}

	default String[] nextLines() {
		List<String> lines = new ArrayList<>();
		while (hasNextLine()) {
			String line = nextLine().trim();
			if (line.length() == 0)
				continue;
			lines.add(line);
		}
		return lines.toArray(new String[0]);
	}

	default Object buildInternClassObject(String internClass, Object... fieldValues) {
		return imp().buildInternClassObject(internClass, fieldValues);
	}

	default void setDataValues(Object value1, Object... otherValues) {
		// System.out.println(value1.getClass().getName());
		if (value1 instanceof Collection)
			value1 = Utilities.convert((Collection<?>) value1);
		if (value1 instanceof Stream)
			value1 = Utilities.convert((Stream<?>) value1);
		for (int i = 0; i < otherValues.length; i++) {
			// System.out.println(otherValues[i].getClass().getName());
			if (otherValues[i] instanceof Collection)
				otherValues[i] = Utilities.convert((Collection<?>) otherValues[i]);
			if (otherValues[i] instanceof Stream)
				otherValues[i] = Utilities.convert((Stream<?>) otherValues[i]);
		}
		imp().setDataValues(value1, otherValues);
	}

	public interface ReaderTxt extends ReaderFile {

		default int nextInt() {
			return imp().fileScanner().nextInt();
		}

		default long nextLong() {
			return imp().fileScanner().nextLong();
		}

	}

	public interface ReaderDzn extends ReaderFile {

		static String formLine(Scanner in) {
			String s = "";
			String line = in.nextLine().trim();
			while (!line.endsWith(";")) {
				if (!line.startsWith("%") && line.length() > 0)
					s += line;
				if (!in.hasNext())
					return s;
				line = in.nextLine().trim();
			}
			return s + line;
		}

		default int nextInt() {
			String s = formLine(imp().fileScanner());
			return Integer.parseInt(s.substring(s.indexOf("=") + 1, s.indexOf(";")).trim());
		}

		default int[] nextInt1D() {
			String s = formLine(imp().fileScanner());
			return Stream.of(s.substring(s.indexOf("[") + 1, s.lastIndexOf("]")).split("\\s*,\\s*")).mapToInt(tok -> Integer.parseInt(tok.trim())).toArray();
		};

		default String[] nextString1D() {
			String s = formLine(imp().fileScanner());
			return Stream.of(s.substring(s.indexOf("[") + 1, s.lastIndexOf("]")).split("\\s*,\\s*")).map(tok -> tok.substring(1, tok.length() - 1))
					.toArray(String[]::new);
		};

		default int[][] nextInt2D() {
			String s = formLine(imp().fileScanner());
			return Stream.of(s.substring(s.indexOf("|") + 1, s.lastIndexOf("|")).split("\\s*\\|\\s*"))
					.map(l -> Stream.of(l.split("\\s*,\\s*")).mapToInt(tok -> Integer.parseInt(tok.trim())).toArray()).toArray(int[][]::new);
		};

		default int[][] nextInt2Db() {
			Scanner in = imp().fileScanner();
			List<String> list = new ArrayList<>();
			String s = in.nextLine().trim();
			list.add(s.substring(s.indexOf("[") + 1));
			while (!s.endsWith(";")) {
				s = in.nextLine().trim();
				list.add(s.endsWith(";") ? s.substring(0, s.lastIndexOf("]")) : s);
			}
			return list.stream().filter(l -> l.length() > 0).map(l -> Stream.of(l.split("\\s*,\\s*")).mapToInt(tok -> Integer.parseInt(tok.trim())).toArray())
					.toArray(int[][]::new);
		};

		default int[][] nextInt2Dc() {
			String s = formLine(imp().fileScanner());
			return Stream.of(s.substring(s.indexOf("{") + 1, s.lastIndexOf("}")).split("\\s*\\}\\s*,\\s*\\{\\s*"))
					.map(l -> Stream.of(l.split("\\s*,\\s*")).mapToInt(tok -> Integer.parseInt(tok.trim())).sorted().toArray()).toArray(int[][]::new);
		};

	}

	public interface ReaderEssence extends ReaderFile {

		default int nextInt() {
			String s = imp().fileScanner().nextLine().trim();
			while (!s.contains("="))
				s = imp().fileScanner().nextLine().trim();
			return Integer.parseInt(s.substring(s.indexOf("=") + 1).trim());
		}

		default int[][] nextInt2D() {
			String s = "";
			String line = imp().fileScanner().nextLine().trim();
			while (!line.endsWith("]]")) {
				s += line;
				line = imp().fileScanner().nextLine().trim();
			}
			s = s + line;
			s = s.substring(s.indexOf("[[") + 2, s.indexOf("]]"));
			return Stream.of(s.split("\\],\\[")).map(t -> Stream.of(t.split(",")).mapToInt(v -> Integer.parseInt(v)).toArray()).toArray(int[][]::new);
		};

	}

}