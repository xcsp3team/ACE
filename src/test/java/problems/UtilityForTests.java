package problems;

import java.io.File;
import java.io.FileOutputStream;
import java.net.URL;
import java.nio.channels.Channels;
import java.util.Collection;
import java.util.stream.Stream;

import dashboard.Arguments;
import executables.Extraction;
import executables.Resolution;

public class UtilityForTests {
	public static String downloadDirectory = "/tmp/";
	public static String webDirectory = "http://www.cril.univ-artois.fr/~lecoutre/instances/";

	public static void load(String... fileNames) {
		for (String fileName : fileNames) {
			try {
				if (!new File(downloadDirectory + fileName).exists()) {
					System.out.println("Downloading instance file " + fileName + " from " + webDirectory + "...");
					FileOutputStream fos = new FileOutputStream(downloadDirectory + fileName);
					fos.getChannel().transferFrom(Channels.newChannel(new URL(webDirectory + fileName).openStream()), 0, 1 << 24);
					fos.close();
					System.out.println("Download of " + fileName + " complete !");
				} else
					System.out.println("Instance " + fileName + " already present in " + downloadDirectory);
			} catch (Exception e) {
				System.out.println("Error while loading web instance files.");
			}
		}
	}

	public static Resolution runResolution(String args, boolean extraction) {
		System.out.println("Command : " + args);
		Arguments.loadArguments(args.split("\\s+"));
		Resolution resolution = extraction ? new Extraction() : new Resolution();
		try {
			resolution.start();
			resolution.join();
		} catch (InterruptedException e) {
			System.out.println("Job interrupted.");
			return null;
		}
		return resolution;
	}

	public static Resolution runResolution(String args) {
		return runResolution(args, false);
	}

	public static Extraction runExtraction(String args) {
		return (Extraction) runResolution(args, true);
	}

	public static Collection<Object[]> dataForCoreExtraction(Collection<Object[]> collection, Object[][] m, Class<?> clazz) {
		Stream.of(m).map(t -> new Object[] { clazz.getName() + " " + downloadDirectory + t[0] + " -e_nc=1 -r_c=50 -l_ng= -v=0 -ev", t[1] })
				.forEach(o -> collection.add(o));
		return collection;
	}

	public static Collection<Object[]> dataForWrongDecisions(Collection<Object[]> collection, Object[][] m, Class<?> clazz) {
		Stream.of(m).map(t -> new Object[] { clazz.getName() + " " + downloadDirectory + t[0] + " -v=0 -ev", t[1] }).forEach(o -> collection.add(o));
		return collection;
	}

}
