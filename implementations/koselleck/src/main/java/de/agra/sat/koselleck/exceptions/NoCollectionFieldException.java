package de.agra.sat.koselleck.exceptions;

/** imports */
import java.lang.reflect.Field;

/**
 * NoCollectionFieldException is a runtime exception that is thrown if the
 *  field is not, as expected, a collection field (assignable from Collection).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NoCollectionFieldException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -2148461436638761099L;

	/**
	 * Constructor for a new NoCollectionFieldException.
	 * 
	 * @param field the field that was expected to be a collection field
	 */
	public NoCollectionFieldException(Field field) {
		super("field \"" + field.getName() + "\" is not a collection field (assignable from Collection)");
	}
}
