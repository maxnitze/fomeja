package de.agra.sat.koselleck.exceptions;

/**
 * 
 * @author Max Nitze
 */
public class NoSuchFieldForClassException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -626444409422933899L;
	
	/**
	 * 
	 * @param constraintFieldName
	 * @param declaringClass
	 */
	public NoSuchFieldForClassException(String constraintFieldName, Class<?> declaringClass) {
		super("no such field \"" + constraintFieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"");
	}
}
