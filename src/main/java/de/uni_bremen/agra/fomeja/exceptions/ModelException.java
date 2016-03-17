package de.uni_bremen.agra.fomeja.exceptions;

/**
 * ModelException COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class ModelException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -567604693135292796L;

	/**
	 * COMMENT
	 * 
	 * @param message the message of the exception
	 */
	public ModelException(String message) {
		super(message);
	}
}
