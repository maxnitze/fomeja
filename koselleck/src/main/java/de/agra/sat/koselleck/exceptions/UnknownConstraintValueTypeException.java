package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintValueType;

/**
 * 
 * @author Max Nitze
 */
public class UnknownConstraintValueTypeException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = 4097976779093367216L;

	/**
	 * 
	 * @param constraintValueType
	 */
	public UnknownConstraintValueTypeException(ConstraintValueType constraintValueType) {
		super("constraint value type " + (constraintValueType == null ? "null" : "\"" + constraintValueType.name + "\"") + " is not known");
	}
}
