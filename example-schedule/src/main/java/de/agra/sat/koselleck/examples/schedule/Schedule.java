package de.agra.sat.koselleck.examples.schedule;

/** imports */
import java.util.List;

import de.agra.sat.koselleck.annotations.Constraint;

/**
 * 
 * @author Max Nitze
 */
public class Schedule {
	/**  */
	public final List<Employee> employees;
	/**  */
	public final List<Task> tasks;
	
	/**
	 * 
	 * @param employees
	 * @param tasks
	 */
	public Schedule(List<Employee> employees, List<Task> tasks) {
		this.employees = employees;
		this.tasks = tasks;
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
		for(Task dependentTask : task.dependentTasks)
			if(dependentTask.start + dependentTask.duration >= task.start)
				return false;
		
		return true;
	}
}
