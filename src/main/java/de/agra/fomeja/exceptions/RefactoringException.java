package de.agra.fomeja.exceptions;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class RefactoringException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -2148461436638761099L;

	/**
	 * COMMENT
	 * 
	 * @param message
	 */
	public RefactoringException(String message) {
		super(message);
	}
}
