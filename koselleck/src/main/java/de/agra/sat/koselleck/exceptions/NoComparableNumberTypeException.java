package de.agra.sat.koselleck.exceptions;

/** imports */
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteral;

/**
 * NoComparableNumberType is a runtime exception that is thrown if the
 *  abstract constraint literal has no comparable number type.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class NoComparableNumberTypeException extends RuntimeException {
	/** serial id */
	private static final long serialVersionUID = 6887195655605180373L;
	
	/**
	 * Constructor for a new NoComparableNumberType.
	 * 
	 * @param constraintLiteral the abstract constraint literal of the
	 *  exception
	 */
	public NoComparableNumberTypeException(AbstractConstraintLiteral<?> constraintLiteral) {
		super("abstract constraint literal \"" + constraintLiteral + "\" has no comparable number type");
	}
}
