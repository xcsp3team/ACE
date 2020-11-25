package optimization;

public interface Optimizable {

	long limit();

	void limit(long newLimit);

	long minComputableObjectiveValue();

	long maxComputableObjectiveValue();

	long minCurrentObjectiveValue();

	long maxCurrentObjectiveValue();

	long objectiveValue();
}
