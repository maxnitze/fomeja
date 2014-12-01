package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractPrematureConstraintValueConstraint;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.utils.ConstraintUtils;

/**
 * AbstractSingleConstraint represents a single constraint in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSingleConstraint extends AbstractConstraint {
	/** the first value */
	private AbstractConstraintValue value1;
	/** the second value */
	private AbstractConstraintValue value2;
	/** the constraint operator of the values */
	private final ConstraintOperator operator;

	/**
	 * Constructor for a new abstract single constraint.
	 * 
	 * @param value1 the new first value
	 * @param operator the new constraint operator of the values
	 * @param value2 the new second value
	 * @param preFields
	 */
	public AbstractSingleConstraint(AbstractConstraintValue value1, ConstraintOperator operator, AbstractConstraintValue value2) {
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public AbstractConstraintValue getValue1() {
		return this.value1;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraintValue getValue2() {
		return this.value2;
	}

	/**
	 * 
	 * @return
	 */
	public ConstraintOperator getOperator() {
		return this.operator;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();

		if (this.value1 instanceof AbstractConstraintLiteral<?> && this.value2 instanceof AbstractConstraintLiteral<?>)
			return ConstraintUtils.evaluate(
					(AbstractConstraintLiteral<?>) this.value1, this.operator, (AbstractConstraintLiteral<?>) this.value2, this);
		else if ((this.value1 instanceof AbstractPrematureConstraintValueConstraint && this.value2 instanceof AbstractConstraintLiteral<?>)
				|| (this.value1 instanceof AbstractConstraintLiteral<?> && this.value2 instanceof AbstractPrematureConstraintValueConstraint)) {
			AbstractPrematureConstraintValueConstraint prematureConstraintValue;
			ConstraintOperator operator;
			if (this.value1 instanceof AbstractPrematureConstraintValueConstraint && this.value2 instanceof AbstractConstraintLiteral<?>) {
				prematureConstraintValue = (AbstractPrematureConstraintValueConstraint) this.value1;
				if (((AbstractConstraintLiteral<?>) this.value2).getValue().equals(0))
					operator = this.operator;
				else
					operator = this.operator.getOpposite();
			} else {
				prematureConstraintValue = (AbstractPrematureConstraintValueConstraint) this.value2;
				if (((AbstractConstraintLiteral<?>) this.value1).getValue().equals(0))
					operator = this.operator.getSwapped();
				else
					operator = this.operator.getSwapped().getOpposite();
			}

			switch (operator) {
			case EQUAL:
				return new AbstractNotConstraint(
						prematureConstraintValue.getConstraint());
			case NOT_EQUAL:
				return prematureConstraintValue.getConstraint();
			case GREATER:
			case GREATER_EQUAL:
			case LESS:
			case LESS_EQUAL:
				Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not supported to check on a constraint, only equality checks are supported ([not] equal) are");
				throw new UnknownConstraintOperatorException(operator);
			default:
				Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator);
			}
		} else
			return this;
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		this.value1 = this.value1.substitute(constraintArguments);
		this.value2 = this.value2.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		unfinishedConstraintLiterals.addAll(this.value1.getUnfinishedConstraintLiterals());
		unfinishedConstraintLiterals.addAll(this.value2.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof AbstractSingleConstraint))
			return false;

		AbstractSingleConstraint singleConstraint = (AbstractSingleConstraint) obj;

		return (
				(this.value1.equals(singleConstraint.value1) &&
						this.value2.equals(singleConstraint.value2) &&
						(this.operator == singleConstraint.operator)) ||
				(this.value1.equals(singleConstraint.value2) &&
						this.value2.equals(singleConstraint.value1) &&
						(this.operator == ConstraintOperator.fromSwappedAsciiName(singleConstraint.operator.getOpcode()))));
	}

	@Override
	public AbstractConstraint clone() {
		return new AbstractSingleConstraint(
				this.value1.clone(), this.operator, this.value2.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append(this.value1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.operator.getAsciiName());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.value2.toString());
		return stringRepresentation.toString();
	}
}
