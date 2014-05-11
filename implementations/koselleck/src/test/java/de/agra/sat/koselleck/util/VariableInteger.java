package de.agra.sat.koselleck.util;

/** imports */
import de.agra.sat.koselleck.annotations.Variable;

/**
 * 
 * @author Max Nitze
 */
public class VariableInteger {
	/** the variable integer value */
	@Variable
	public int integerValue;

	/**
	 * getter method for the variable integer value.
	 * 
	 * @return the variable integer value
	 */
	public int getIntegerValue() {
		return this.integerValue;
	}
}
