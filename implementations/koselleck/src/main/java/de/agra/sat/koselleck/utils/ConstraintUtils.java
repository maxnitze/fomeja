package de.agra.sat.koselleck.utils;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraintLiteralField;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.types.ConstraintOperator;

/**
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public final class ConstraintUtils {
	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private ConstraintUtils() {}

	/**
	 * 
	 * @param constraintLiteral1
	 * @param operator
	 * @param constraintLiteral2
	 * @param backupConstraint
	 * 
	 * @return
	 */
	public static AbstractConstraint evaluate(AbstractConstraintLiteral<?> constraintLiteral1, ConstraintOperator operator, AbstractConstraintLiteral<?> constraintLiteral2, AbstractConstraint backupConstraint) {
		if (constraintLiteral1.isNumberType && constraintLiteral2.isNumberType)
			return evaluateNumberTypes(constraintLiteral1, operator, constraintLiteral2);
		else if (constraintLiteral1 instanceof AbstractConstraintLiteralField
				&& constraintLiteral2 instanceof AbstractConstraintLiteralField
				&& ((AbstractConstraintLiteralField)constraintLiteral1).equals((AbstractConstraintLiteralField)constraintLiteral1)) {
			switch(operator) {
			case EQUAL:
				return new AbstractBooleanConstraint(true);
			case GREATER:
				return new AbstractBooleanConstraint(false);
			case GREATER_EQUAL:
				return new AbstractBooleanConstraint(true);
			case LESS:
				return new AbstractBooleanConstraint(false);
			case LESS_EQUAL:
				return new AbstractBooleanConstraint(true);
			case NOT_EQUAL:
				return new AbstractBooleanConstraint(false);
			default:
				Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator);
			}
		} else
			return backupConstraint;
	}

	/**
	 * evaluate evaluates the given constraintLiterals to its abstract
	 *  boolean value considering the operator.
	 * 
	 * @param constraintLiteral1 the first constraint literal
	 * @param operator the operator of the single constraint
	 * @param constraintLiteral2 the second constraint literal
	 * 
	 * @return the abstract boolean value of the given comparable values
	 *  considering the operator
	 */
	public static AbstractBooleanConstraint evaluateNumberTypes(AbstractConstraintLiteral<?> constraintLiteral1, ConstraintOperator operator, AbstractConstraintLiteral<?> constraintLiteral2) {
		switch(operator) {
		case EQUAL:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) == 0);
		case GREATER:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) > 0);
		case GREATER_EQUAL:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) >= 0);
		case LESS:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) < 0);
		case LESS_EQUAL:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) <= 0);
		case NOT_EQUAL:
			return new AbstractBooleanConstraint(constraintLiteral1.compareTo(constraintLiteral2) != 0);
		default:
			Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownConstraintOperatorException(operator);
		}
	}
}
