package de.agra.sat.koselleck.exceptions;

/**
 * UnknownSwitchCaseException is a runtime exception that is thrown when an
 *  unknown switch case is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownSwitchCaseException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 1831323514388130055L;

	/**
	 * Constructor for a new UnknownSwitchCaseException.
	 * 
	 * @param message the message of the exception
	 */
	public UnknownSwitchCaseException(String message) {
		super(message);
	}
}
