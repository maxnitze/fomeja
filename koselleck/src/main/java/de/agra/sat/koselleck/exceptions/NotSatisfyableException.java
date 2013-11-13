package de.agra.sat.koselleck.exceptions;

/**
 * NotSatisfyableException is an exception that is thrown when a given instance
 *  is not satisfiable.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NotSatisfyableException extends Exception {
	/** serial id */
	private static final long serialVersionUID = -8804853833981840506L;
	
	/**
	 * Constructor for a new NotSatisfyableException.
	 * 
	 * @param message the message of the exception
	 */
	public NotSatisfyableException(String message) {
		super(message);
	}
}
