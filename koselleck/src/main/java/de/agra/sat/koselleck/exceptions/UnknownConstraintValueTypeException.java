package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintValueType;

/**
 * UnknownConstraintValueTypeException is a runtime exception that is thrown
 *  when an unknown constraint value type is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnknownConstraintValueTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 4097976779093367216L;

	/**
	 * Constructor for a new UnknownConstraintValueTypeException.
	 * 
	 * @param constraintValueType the unknown constraint value type
	 */
	public UnknownConstraintValueTypeException(ConstraintValueType constraintValueType) {
		super("constraint value type " + (constraintValueType == null ? "null" : "\"" + constraintValueType.name + "\"") + " is not known");
	}
}
