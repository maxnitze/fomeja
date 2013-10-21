package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * 
 * @author Max Nitze
 */
public enum ArithmeticOperator {
	ADD("+"),
	SUB("-"),
	MUL("*"),
	DIV("/");
	
	/**  */
	public final String asciiName;
	
	/**
	 * 
	 * @param asciiName
	 */
	ArithmeticOperator(String asciiName) {
		this.asciiName = asciiName;
	}
}
