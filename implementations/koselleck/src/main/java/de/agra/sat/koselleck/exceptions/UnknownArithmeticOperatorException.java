package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * UnknownArithmeticOperatorException is a runtime exception that is thrown
 *  when an unknown arithmetic operator is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownArithmeticOperatorException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -1818258361684012888L;

	/**
	 * Constructor for a new UnknownArithmeticOperatorException.
	 * 
	 * @param operator the unknown arithmetic operator
	 */
	public UnknownArithmeticOperatorException(ArithmeticOperator operator) {
		super("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
	}
}
