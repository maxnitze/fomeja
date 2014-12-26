package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;

/**
 * UnsupportedConstraintLiteralException ... COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedConstraintLiteralException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -7233559166432261684L;

	/**
	 * Constructor for a new UnsupportedConstraintValueException.
	 * 
	 * @param constraintValue the unsupported abstract constraint value
	 */
	public UnsupportedConstraintLiteralException(AbstractConstraintLiteral<?> constraintLiteral) {
		super("constraint value type \"" + (constraintLiteral == null ? "null" : constraintLiteral.getClass().getSimpleName()) + "\" is not supported");
	}
}
