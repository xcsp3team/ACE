package problems;

import dashboard.Arguments;
import main.Extraction;
import main.Head;

public class UtilityForTests {

	public static Head runResolution(String args, boolean extraction) {
		System.out.println("Command : " + args);
		Arguments.loadArguments(args.split("\\s+"));
		Head resolution = extraction ? new Extraction() : new Head();
		try {
			resolution.start();
			resolution.join();
		} catch (InterruptedException e) {
			System.out.println("Job interrupted.");
			return null;
		}
		return resolution;
	}

	public static Head runResolution(String args) {
		return runResolution(args, false);
	}

	public static Extraction runExtraction(String args) {
		return (Extraction) runResolution(args, true);
	}
}
