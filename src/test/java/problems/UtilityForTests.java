package problems;

import dashboard.Arguments;
import executables.Extraction;
import executables.Resolution;

public class UtilityForTests {

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
}
