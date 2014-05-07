package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;

/**
 * UnsupportedConstraintException is a  runtime exception that is thrown when a
 *  unsupported abstract constraint is handled.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class UnsupportedConstraintException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = -6276514312554697460L;

	/**
	 * Constructor for a new UnsupportedConstraintException.
	 * 
	 * @param constraint the unknown abstract constraint
	 */
	public UnsupportedConstraintException(AbstractConstraint constraint) {
		super("constraint type \"" + (constraint == null ? "null" : constraint.getClass().getSimpleName()) + "\" is not supported");
	}
}
