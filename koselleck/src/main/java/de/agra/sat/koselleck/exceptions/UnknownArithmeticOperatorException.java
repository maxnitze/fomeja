package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.ArithmeticOperator;

/**
 * 
 * @author Max Nitze
 */
public class UnknownArithmeticOperatorException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -1818258361684012888L;

	/**
	 * 
	 * @param operator
	 */
	public UnknownArithmeticOperatorException(ArithmeticOperator operator) {
		super("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
	}
}
