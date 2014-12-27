package de.agra.sat.koselleck.utils;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.types.ConstraintOperator;

/**
 * COMMENT
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
	 * COMMENT
	 * 
	 * @param constraintLiteral1
	 * @param operator
	 * @param constraintLiteral2
	 * @param backupConstraint
	 * 
	 * @return
	 */
	public static AbstractConstraint evaluate(AbstractConstraintLiteral<?> constraintLiteral1, ConstraintOperator operator, AbstractConstraintLiteral<?> constraintLiteral2, AbstractConstraint backupConstraint) {
		if (constraintLiteral1.isFinishedNumberType() && constraintLiteral2.isFinishedNumberType())
			return evaluateNumberTypes(constraintLiteral1, operator, constraintLiteral2);
		else if (constraintLiteral1.isNumberType() && constraintLiteral2.isNumberType()
				&& constraintLiteral1.equals(constraintLiteral2)) {
			switch (operator) {
			case EQUAL:
			case GREATER_EQUAL:
			case LESS_EQUAL:
				return new AbstractBooleanConstraint(true);
			case GREATER:
			case LESS:
			case NOT_EQUAL:
				return new AbstractBooleanConstraint(false);
			default:
				Logger.getLogger(ConstraintUtils.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator);
			}
		} else if (constraintLiteral1 instanceof AbstractConstraintLiteralObject
				&& constraintLiteral2 instanceof AbstractConstraintLiteralObject
				&& constraintLiteral1.isFinishedType() && constraintLiteral2.isFinishedType()) {
			switch (operator) {
			case EQUAL:
			case GREATER_EQUAL:
			case LESS_EQUAL:
				return new AbstractBooleanConstraint(((AbstractConstraintLiteralObject) constraintLiteral1).getValue() == ((AbstractConstraintLiteralObject) constraintLiteral2).getValue());
			case GREATER:
			case LESS:
			case NOT_EQUAL:
				return new AbstractBooleanConstraint(((AbstractConstraintLiteralObject) constraintLiteral1).getValue() != ((AbstractConstraintLiteralObject) constraintLiteral2).getValue());
			default:
				Logger.getLogger(ConstraintUtils.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator);
			}
		} else
			return backupConstraint;
	}

	/**
	 * COMMENT
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
			Logger.getLogger(ConstraintUtils.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
			throw new UnknownConstraintOperatorException(operator);
		}
	}
}
