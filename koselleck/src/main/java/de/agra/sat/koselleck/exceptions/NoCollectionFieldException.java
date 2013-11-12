package de.agra.sat.koselleck.exceptions;

/** imports */
import java.lang.reflect.Field;

/**
 * 
 * @author Max Nitze
 */
public class NoCollectionFieldException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -2148461436638761099L;

	/**
	 * 
	 * @param field
	 */
	public NoCollectionFieldException(Field field) {
		super("field \"" + field.getName() + "\" is not a collection field (assignable from Collection)");
	}
}
