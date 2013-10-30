package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * An enumeration of the four arithmetic operators +, -, * and /.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ArithmeticOperator {
	ADD("+"),
	SUB("-"),
	MUL("*"),
	DIV("/");
	
	/** the ascii name */
	public final String asciiName;
	
	/**
	 * Constructor for a new arithmetic operator.
	 * 
	 * @param asciiName the new ascii name
	 */
	ArithmeticOperator(String asciiName) {
		this.asciiName = asciiName;
	}
}
