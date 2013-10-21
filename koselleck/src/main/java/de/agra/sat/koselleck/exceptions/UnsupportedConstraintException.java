package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;

/**
 * 
 * @author Max Nitze
 */
public class UnsupportedConstraintException extends RuntimeException {
	/**  */
	private static final long serialVersionUID = -6276514312554697460L;
	
	/**
	 * 
	 * @param constraint
	 */
	public UnsupportedConstraintException(AbstractConstraint constraint) {
		super("constraint type \"" + (constraint == null ? "null" : constraint.getClass().getSimpleName()) + "\" is not supported");
	}
}
