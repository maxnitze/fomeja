package de.agra.sat.koselleck.examples.schedule;

/**
 * 
 * @author Max Nitze
 */
public class Employee {
	/**  */
	public final String firstName;
	/**  */
	public final String lastName;
	/**  */
	public final Skill[] skills;

	/**
	 * 
	 * @param firstName
	 * @param lastName
	 * @param skills
	 */
	public Employee(String firstName, String lastName, Skill[] skills) {
		this.firstName = firstName;
		this.lastName = lastName;
		this.skills = skills;
	}

	/**
	 * 
	 * @param neededSkills
	 * 
	 * @return
	 */
	public boolean hasSkills(Skill[] neededSkills) {
		for(Skill neededSkill : neededSkills) {
			boolean found = false;
			for(Skill skill : this.skills) {
				if(skill == neededSkill) {
					found = true;
					break;
				}
			}
			if(!found)
				return false;
		}

		return true;
	}
}
