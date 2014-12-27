package de.agra.sat.koselleck.examples;

import java.util.ArrayList;
import java.util.List;

import de.agra.sat.koselleck.DIAB;
import de.agra.sat.koselleck.examples.schedule.Employee;
import de.agra.sat.koselleck.examples.schedule.Schedule;
import de.agra.sat.koselleck.examples.schedule.Skill;
import de.agra.sat.koselleck.examples.schedule.Task;

public class SchedulingProblem {
	public static void main(String[] args) {
		boolean testValidate	= false;
		boolean testSatisfy		= true;
		boolean testMinimize	= false;
		boolean testMaximize	= false;

		List<Employee> employees = new ArrayList<Employee>();
		employees.add(new Employee("Firstname1", "Lastname1", Skill.JAVA, new Skill[] { Skill.JAVA, Skill.MANAGEMENT }));
		employees.add(new Employee("Firstname2", "Lastname2", Skill.CPP, new Skill[] { Skill.CPP, Skill.MANAGEMENT }));
		employees.add(new Employee("Firstname3", "Lastname3", Skill.C, new Skill[] { Skill.C, Skill.JAVA }));
		employees.add(new Employee("Firstname4", "Lastname4", Skill.MANAGEMENT, new Skill[] { Skill.C, Skill.CPP, Skill.MANAGEMENT }));
		employees.add(new Employee("Firstname5", "Lastname5", Skill.JAVA, new Skill[] { Skill.JAVA, Skill.CPP }));

		List<Task> tasks = new ArrayList<Task>();
		Task task1 = new Task("Task1", 2, Skill.JAVA, new Skill[] { Skill.JAVA }, null, new Task[] {});
		tasks.add(task1);
		Task task2 = new Task("Task2", 1, Skill.C, new Skill[] { Skill.C }, null, new Task[] { task1 });
		tasks.add(task2);
		Task task3 = new Task("Task3", 4, Skill.CPP, new Skill[] { Skill.CPP }, null, new Task[] { task1 });
		tasks.add(task3);
		Task task4 = new Task("Task4", 6, Skill.MANAGEMENT, new Skill[] { Skill.MANAGEMENT }, null, new Task[] {});
		tasks.add(task4);
		Task task5 = new Task("Task4", 6, Skill.MANAGEMENT, new Skill[] { Skill.MANAGEMENT }, null, new Task[] {});
		tasks.add(task5);

		Schedule schedule = new Schedule(employees, tasks);

		if (testValidate) {
			if (DIAB.validate(schedule))
				System.out.println("the current schedule is valid");
			else
				System.out.println("the current schedule is not valid");
		}

		if (testSatisfy) {
			if (DIAB.satisfy(schedule))
				System.out.println("there is a valid schedule for these tasks");
			else
				System.out.println("there is no valid schedule for these tasks");
		}

		if (testMinimize) {
			DIAB.minimize(schedule);
		}

		if (testMaximize) {
			DIAB.maximize(schedule);
		}
	}
}
