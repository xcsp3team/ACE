package problems.todo;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;
import java.util.stream.IntStream;

import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

public class Timetabling implements ProblemAPI {

	int[] roomSizes;
	int[][] attends, roomFeature, eventFeature, eventSlot, eventEvent;

	void data() {
		String fileName = imp().askString("Enter data filename");
		try (Scanner scanner = new Scanner(new File(fileName))) {
			int nbEvents = scanner.nextInt();
			int nbRooms = scanner.nextInt();
			int nbFeatures = scanner.nextInt();
			int nbStudents = scanner.nextInt();
			roomSizes = IntStream.range(0, nbRooms).map(i -> scanner.nextInt()).toArray();
			System.out.println("t=" + Kit.join(roomSizes));
			attends = IntStream.range(0, nbStudents).mapToObj(i -> IntStream.range(0, nbEvents).map(j -> scanner.nextInt()).toArray()).toArray(int[][]::new);
			System.out.println("att=" + Kit.join(attends));
			roomFeature = IntStream.range(0, nbRooms).mapToObj(i -> IntStream.range(0, nbFeatures).map(j -> scanner.nextInt()).toArray()).toArray(int[][]::new);
			System.out.println("rf=" + Kit.join(roomFeature));
			eventFeature = IntStream.range(0, nbEvents).mapToObj(i -> IntStream.range(0, nbFeatures).map(j -> scanner.nextInt()).toArray())
					.toArray(int[][]::new);
			System.out.println("ef=" + Kit.join(eventFeature));
			if (!scanner.hasNext()) {
				System.out.println("returned");
				return;
			}
			int nbSlots = 45;
			eventSlot = IntStream.range(0, nbEvents).mapToObj(i -> IntStream.range(0, nbSlots).map(j -> scanner.nextInt()).toArray()).toArray(int[][]::new);
			System.out.println("es=" + Kit.join(eventSlot));
			eventEvent = IntStream.range(0, nbEvents).mapToObj(i -> IntStream.range(0, nbEvents).map(j -> scanner.nextInt()).toArray()).toArray(int[][]::new);
			System.out.println("ee=" + Kit.join(eventEvent));

		} catch (FileNotFoundException e) {
			Kit.exit("Error with File " + fileName, e);
		}
	}

	@Override
	public void model() {
		// VarInteger x = var("x", dom(0, 1));
	}
}
