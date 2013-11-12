package de.agra.sat.koselleck.exceptions;

/** imports */
import java.lang.reflect.Method;

/**
 * 
 * @author Max Nitze
 */
public class NoConstraintMethodException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -887113639393430230L;
	
	/**
	 * 
	 * @param message
	 */
	public NoConstraintMethodException(Method method) {
		super("method \"" + method.toGenericString() + "\" is not a constraint method");
	}
}
