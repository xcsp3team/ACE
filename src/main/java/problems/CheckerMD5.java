package problems;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Scanner;
import java.util.stream.Collectors;

import utility.Kit;

// find . -name "*.lzma" -print0 | sort -z | xargs -r0 md5sum > md5SumOutput
// java problems.CheckerMD5 md5SumOutput > doublonsMD5
public class CheckerMD5 {
	public static void main(String[] args) {
		if (args.length != 1) {
			System.out.println("usage: java " + CheckerMD5.class.getName() + " <fileWithAllMD5>");
			return;
		}
		File f = new File(args[0]);
		Map<String, List<String>> map = new LinkedHashMap<>();
		try (Scanner scanner = new Scanner(f)) {
			while (scanner.hasNext()) {
				String line = scanner.nextLine().trim();
				if (line.length() == 0)
					continue;
				String[] t = line.split("\\s+");
				map.computeIfAbsent(t[0], k -> new LinkedList<>()).add(t[1]);
			}
		} catch (FileNotFoundException e) {
			Kit.exit("Error with " + args[0], e);
		}
		for (Entry<String, List<String>> entry : map.entrySet())
			if (entry.getValue().size() > 1)
				System.out.println(entry.getKey() + " : " + entry.getValue().stream().collect(Collectors.joining(", ")));
	}
}
