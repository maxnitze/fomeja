package de.agra.sat.koselleck.examples.schedule;

/** imports */
import de.agra.sat.koselleck.annotations.Variable;

/**
 * 
 * @author Max Nitze
 */
public class Task {
	/**  */
	public final String name;
	/**  */
	public final int duration;
	/**  */
	public final Skill[] neededSkills;
	/**  */
	public final Task[] dependentTasks;
	
	/**  */
	@Variable
	public int start;
	
	/**  */
	@Variable
	public Employee doneBy;
	
	/**
	 * 
	 * @param name
	 * @param duration
	 * @param neededSkills
	 * @param dependentTasks
	 */
	public Task(String name, int duration, Skill[] neededSkills, Task[] dependentTasks) {
		this.name = name;
		this.duration = duration;
		this.neededSkills = neededSkills;
		this.dependentTasks = dependentTasks;
	}
	
	/**
	 * 
	 * @param task
	 * 
	 * @return
	 */
	public boolean intersectsWith(Task task) {
		return (this.start >= task.start && this.start < task.start + task.duration)
				|| (task.start >= this.start && task.start < this.start + this.duration);
	}
}
