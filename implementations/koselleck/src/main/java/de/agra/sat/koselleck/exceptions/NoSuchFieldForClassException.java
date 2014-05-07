package de.agra.sat.koselleck.exceptions;

/**
 * NoSuchFieldForClassException is a runtime exception that is thrown when a
 *  field, that was expected to be part of a class, is not.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NoSuchFieldForClassException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -626444409422933899L;

	/**
	 * Constructor for a new NoSuchFieldForClassException.
	 * 
	 * @param fieldName the name of the field
	 * @param declaringClass the expected declaring class of the field
	 */
	public NoSuchFieldForClassException(String fieldName, Class<?> declaringClass) {
		super("no such field \"" + fieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"");
	}
}
