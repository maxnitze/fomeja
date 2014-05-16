package de.agra.sat.koselleck.util;

/** imports */
import java.util.Set;

import de.agra.sat.koselleck.annotations.Constraint;

/**
 * 
 * @author Max Nitze
 */
public class VariableIntegers {
	/**  */
	private Set<VariableInteger> variableIntegers;

	/**
	 * 
	 * @param variableIntegers
	 */
	public VariableIntegers(Set<VariableInteger> variableIntegers) {
		this.variableIntegers = variableIntegers;
	}

	/** constraints
	 * ----- ----- ----- ----- ----- */

	@Constraint(fields = { @Constraint.Field(""), @Constraint.Field("") })
	public boolean variableIntegersDiffer(VariableInteger variableInteger1, VariableInteger variableInteger2) {
		return variableInteger1 == variableInteger2 || variableInteger1.integerValue != variableInteger2.integerValue;
	}

	@Constraint(fields = { @Constraint.Field("variableIntegers"), @Constraint.Field("variableIntegers") })
	public boolean variableIntegersDifferGivenFieldName(VariableInteger variableInteger1, VariableInteger variableInteger2) {
		return variableInteger1 == variableInteger2 || variableInteger1.integerValue != variableInteger2.integerValue;
	}

	@Constraint(fields = { @Constraint.Field(""), @Constraint.Field("") })
	public boolean variableIntegersDifferByGetter(VariableInteger variableInteger1, VariableInteger variableInteger2) {
		return variableInteger1 == variableInteger2 || variableInteger1.getIntegerValue() != variableInteger2.getIntegerValue();
	}

	@Constraint(fields = { @Constraint.Field("variableIntegers"), @Constraint.Field("variableIntegers") })
	public boolean variableIntegersDifferByGetterGivenFieldName(VariableInteger variableInteger1, VariableInteger variableInteger2) {
		return variableInteger1 == variableInteger2 || variableInteger1.getIntegerValue() != variableInteger2.getIntegerValue();
	}

	/** getter / setter
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public Set<VariableInteger> getVariableIntegers() {
		return this.variableIntegers;
	}
}
