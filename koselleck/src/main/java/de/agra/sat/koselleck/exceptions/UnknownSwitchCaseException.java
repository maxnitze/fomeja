package de.agra.sat.koselleck.exceptions;

/**
 * 
 * @author Max Nitze
 */
public class UnknownSwitchCaseException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = 1831323514388130055L;

	/**
	 * 
	 * @param message
	 */
	public UnknownSwitchCaseException(String message) {
		super(message);
	}
}
