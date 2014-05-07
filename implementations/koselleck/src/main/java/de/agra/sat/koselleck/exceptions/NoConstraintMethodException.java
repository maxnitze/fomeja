package de.agra.sat.koselleck.exceptions;

/** imports */
import java.lang.reflect.Method;

/**
 * NoConstraintMethodExcpetion is a runtime exception that is thrown if the
 *  method is not, as expected, annotated with Constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NoConstraintMethodException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -887113639393430230L;

	/**
	 * Constructor for a new NoConstraintMethodException.
	 * 
	 * @param method the method of the exception
	 */
	public NoConstraintMethodException(Method method) {
		super("method \"" + method.toGenericString() + "\" is not a constraint method");
	}
}
