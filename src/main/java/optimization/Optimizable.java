package optimization;

public interface Optimizable {

	long getLimit();

	void setLimit(long newLimit);

	long minComputableObjectiveValue();

	long maxComputableObjectiveValue();

	long minCurrentObjectiveValue();

	long maxCurrentObjectiveValue();

	long objectiveValue();
}
