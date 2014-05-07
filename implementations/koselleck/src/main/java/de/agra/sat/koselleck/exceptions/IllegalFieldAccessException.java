package de.agra.sat.koselleck.exceptions;

/** imports */
import java.lang.reflect.Field;

/**
 * IllegalFieldAccessException is a runtime exception that is thrown when a
 *  field was accessed though it is not accessible.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class IllegalFieldAccessException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -2502006321320375209L;

	/**
	 * Constructor for a new IllegalFieldAccessException.
	 * 
	 * @param field the illegal accessed field
	 */
	public IllegalFieldAccessException(Field field) {
		super("could not access field \"" + field.getName() +"\"");
	}
}
