package de.agra.sat.koselleck.examples.schedule;

/** imports */
import java.util.List;

import de.agra.sat.koselleck.annotations.Constraint;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class Schedule {
	/** COMMENT */
	public final List<Employee> employees;
	/** COMMENT */
	public final List<Task> tasks;

	/** COMMENT */
	private final int taskStart;

	/**
	 * COMMENT
	 * 
	 * @param employees
	 * @param tasks
	 */
	public Schedule(List<Employee> employees, List<Task> tasks) {
		this.employees = employees;
		this.tasks = tasks;

		this.taskStart = 5;
	}

	/**
	 * COMMENT
	 * 
	 * @param task
	 * 
	 * @return
	 */
	@Constraint(fields = { @Constraint.Field("tasks") })
	public boolean startIsGETaskStart(Task task) {
		return task.start >= this.taskStart;
	}

	/**
	 * 
	 * @param task1
	 * @param task2
	 * 
	 * @return
	 */
	@Constraint(fields = { @Constraint.Field("tasks"), @Constraint.Field("tasks") })
	public boolean oneTaskAtATime(Task task1, Task task2) {
		return task1 == task2 || !task1.intersectsWith(task2) || task1.doneBy != task2.doneBy;
	}

	/**
	 * 
	 * @param task
	 * 
	 * @return
	 */
	@Constraint(fields = { @Constraint.Field("tasks") })
	public boolean employeeHasNeededSkill(Task task) {
		return task.neededSkill == task.doneBy.skill;
	}

	/**
	 * 
	 * @param task
	 * 
	 * @return
	 */
//	@Constraint(fields = { @Constraint.Field("tasks") })
	public boolean employeeHasNeededSkills(Task task) {
		return task.doneBy.hasSkills(task.neededSkills);
	}

	/**
	 * 
	 * @param task
	 * 
	 * @return
	 */
//	@Constraint(fields = { @Constraint.Field("tasks") })
	public boolean dependentTasksAreFinished(Task task) {
		for (Task dependentTask : task.dependentTasks)
			if (dependentTask.start + dependentTask.duration >= task.start)
				return false;

		return true;
	}
}
