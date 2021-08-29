package problems;

import dashboard.Input;
import main.Head;
import main.HeadExtraction;

public class UtilityForTests {

	private static Head runHeadMethod(String args, boolean extraction) {
		System.out.println("\nCommand : " + args);
		Input.loadArguments(args.split("\\s+"));
		Head resolution = extraction ? new HeadExtraction() : new Head();
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
		return runHeadMethod(args, false);
	}

	public static HeadExtraction runExtraction(String args) {
		return (HeadExtraction) runHeadMethod(args, true);
	}
}
