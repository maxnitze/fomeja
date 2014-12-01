package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.types.BooleanConnector;
import de.agra.sat.koselleck.types.ConstraintOperator;

/**
 * AbstractSubConstraint represents a sub constraint in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSubConstraint extends AbstractConstraint {
	/** the first constraint */
	private AbstractConstraint constraint1;
	/** the second constraint */
	private AbstractConstraint constraint2;
	/** the boolean connector of both constraints */
	private final BooleanConnector connector;

	/**
	 * Constructor for a new abstract sub constraint.
	 * 
	 * @param constraint1 the new first constraint
	 * @param connector the new boolean connector of both constraints
	 * @param constraint2 the new second constraint
	 */
	public AbstractSubConstraint(AbstractConstraint constraint1, BooleanConnector connector, AbstractConstraint constraint2) {
		this.constraint1 = constraint1;
		this.connector = connector;
		this.constraint2 = constraint2;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getConstraint1() {
		return this.constraint1;
	}

	/**
	 * 
	 * @return
	 */
	public AbstractConstraint getConstraint2() {
		return this.constraint2;
	}

	/**
	 * 
	 * @return
	 */
	public BooleanConnector getConnector() {
		return this.connector;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraint1.replaceAll(regex, replacement);
		this.constraint2.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraint evaluate() {
		this.constraint1 = this.constraint1.evaluate();
		this.constraint2 = this.constraint2.evaluate();

		/** evaluate to boolean if both sub-constraints are boolean
		 * constraints */
		if (
				this.constraint1 instanceof AbstractBooleanConstraint &&
				this.constraint2 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
						((AbstractBooleanConstraint) this.constraint1).getValue(),
						((AbstractBooleanConstraint) this.constraint2).getValue());
		/** evaluate constraint if the first sub-constraints is a boolean
		 * constraint */
		else if (this.constraint1 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
					((AbstractBooleanConstraint) this.constraint1).getValue(),
					this.constraint2);
		/** evaluate constraint if the second sub-constraints is a boolean
		 * constraint */
		else if (this.constraint2 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
					((AbstractBooleanConstraint) this.constraint2).getValue(),
					this.constraint1);
		/** try to evaluate constraint if both sub-constraints are single
		 * constraints */
		else if (
				this.constraint1 instanceof AbstractSingleConstraint &&
				this.constraint2 instanceof AbstractSingleConstraint) {
			AbstractSingleConstraint singleConstraint1 = (AbstractSingleConstraint) this.constraint1;
			AbstractSingleConstraint singleConstraint2 = (AbstractSingleConstraint) this.constraint2;

			/** evaluate to one constraint if both constraints are equal */
			if (singleConstraint1.equals(singleConstraint2))
				return singleConstraint1;
			/** evaluate the constraint if the values of both sub-constraints
			 * are equal */
			else if (
					singleConstraint1.getValue1().equals(singleConstraint2.getValue1()) &&
					singleConstraint1.getValue2().equals(singleConstraint2.getValue2()))
				return evaluateEqualConstraints(
						singleConstraint1.getOperator(),
						singleConstraint2.getOperator());
			/** evaluate the constraint if the values of both sub-constraints
			 * are equal */
			else if (
					singleConstraint1.getValue1().equals(singleConstraint2.getValue2()) &&
					singleConstraint1.getValue2().equals(singleConstraint2.getValue1()))
				return evaluateEqualConstraints(
						singleConstraint1.getOperator(),
						ConstraintOperator.fromSwappedAsciiName(singleConstraint2.getOperator().getAsciiName()));
			else
				return this;
		} else
			return this;
	}

	@Override
	public void substitute(Map<Integer, Object> constraintArguments) {
		this.constraint1.substitute(constraintArguments);
		this.constraint2.substitute(constraintArguments);
	}

	@Override
	public boolean matches(String regex) {
		return this.constraint1.matches(regex) || this.constraint2.matches(regex);
	}

	@Override
	public Set<AbstractConstraintLiteral<?>> getUnfinishedConstraintLiterals() {
		Set<AbstractConstraintLiteral<?>> unfinishedConstraintLiterals = new HashSet<AbstractConstraintLiteral<?>>();
		unfinishedConstraintLiterals.addAll(this.constraint1.getUnfinishedConstraintLiterals());
		unfinishedConstraintLiterals.addAll(this.constraint2.getUnfinishedConstraintLiterals());

		return unfinishedConstraintLiterals;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractSubConstraint))
			return false;

		AbstractSubConstraint subConstraint = (AbstractSubConstraint)object;

		return
				this.constraint1.equals(subConstraint.constraint1) &&
				this.connector == subConstraint.connector &&
				this.constraint2.equals(subConstraint.constraint2);
	}

	@Override
	public AbstractConstraint clone() {
		return new AbstractSubConstraint(
				this.constraint1.clone(), this.connector, this.constraint2.clone());
	}

	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append(this.constraint1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.connector.getCode());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.constraint2.toString());
		return stringRepresentation.toString();
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * evaluateConstraint evaluates the given boolean values considering the
	 *  boolean connector of this abstract sub constraint.
	 * 
	 * @param value1 the first boolean value
	 * @param value2 the second boolean value
	 * 
	 * @return an abstract boolean constraint representing the calculated value
	 *  of the given boolean values and the boolean connector of this abstract
	 *  abstract sub constraint
	 */
	private AbstractConstraint evaluateConstraint(boolean value1, boolean value2) {
		switch(this.connector) {
		case AND:
			return new AbstractBooleanConstraint(value1 && value2);
		case OR:
			return new AbstractBooleanConstraint(value1 || value2);
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.getCode() + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}

	/**
	 * evaluateConstraint evaluates the given boolean value and the given
	 *  abstract constraint considering the boolean connector of this abstract
	 *  sub constraint.
	 * 
	 * @param booleanValue the boolean value
	 * @param constraint the abstract constraint
	 * 
	 * @return an abstract boolean constraint representing a {@code false} if
	 *  the boolean value is {@code false} and the boolean connector of this
	 *  abstract constraint is {@code AND} or the constraint if the boolean
	 *  value is {@code true} or an abstract boolean constraint representing a
	 *  {@code true} if the boolean value is {@code false} and the boolean
	 *  connector of this abstract constraint is {@code OR} or the constraint
	 *  if the boolean value is {@code false}.
	 */
	private AbstractConstraint evaluateConstraint(boolean booleanValue, AbstractConstraint constraint) {
		switch(this.connector) {
		case AND:
			return booleanValue ? constraint : new AbstractBooleanConstraint(false);
		case OR:
			return booleanValue ? new AbstractBooleanConstraint(true) : constraint;
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.getCode() + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}

	/**
	 * evaluateEqualConstraints evaluates the given constraint operators
	 *  considering the boolean connector of this abstract sub constraint.
	 * 
	 * @param operator1 the first constraint operator
	 * @param operator2 the second constraint operator
	 * 
	 * @return an abstract boolean constraint representing a {@code false} if
	 *  the boolean connector of this abstract sub constraint is an {@code AND}
	 *  and the given constraint operators do not match, an abstract boolean
	 *  constraint representing a {@code true} if the boolean connector of this
	 *  abstract sub constraint is an {@code OR} and the given constraint
	 *  operators match 
	 */
	private AbstractConstraint evaluateEqualConstraints(ConstraintOperator operator1, ConstraintOperator operator2) {
		switch(this.connector) {
		case AND:
			switch(operator1) {
			case EQUAL:
				switch(operator2) {
				case GREATER:
				case LESS:
				case NOT_EQUAL:
					return new AbstractBooleanConstraint(false);
				case EQUAL:
				case GREATER_EQUAL:
				case LESS_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case GREATER:
				switch(operator2) {
				case EQUAL:
				case LESS_EQUAL:
				case LESS:
					return new AbstractBooleanConstraint(false);
				case GREATER:
				case GREATER_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case GREATER_EQUAL:
				switch(operator2) {
				case LESS:
					return new AbstractBooleanConstraint(false);
				case EQUAL:
				case GREATER:
				case GREATER_EQUAL:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case LESS:
				switch(operator2) {
				case EQUAL:
				case GREATER_EQUAL:
				case GREATER:
					return new AbstractBooleanConstraint(false);
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case LESS_EQUAL:
				switch(operator2) {
				case GREATER:
					return new AbstractBooleanConstraint(false);
				case EQUAL:
				case GREATER_EQUAL:
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case NOT_EQUAL:
				switch(operator2) {
				case EQUAL:
					return new AbstractBooleanConstraint(false);
				case GREATER:
				case GREATER_EQUAL:
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			default:
				Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator1 == null ? "null" : "\"" + operator1.getAsciiName() + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator1);
			}
		case OR:
			switch(operator1) {
			case EQUAL:
				switch(operator2) {
				case NOT_EQUAL:
					return new AbstractBooleanConstraint(true);
				case EQUAL:
				case GREATER:
				case GREATER_EQUAL:
				case LESS:
				case LESS_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case GREATER:
				switch(operator2) {
				case LESS_EQUAL:
					return new AbstractBooleanConstraint(true);
				case EQUAL:
				case GREATER:
				case GREATER_EQUAL:
				case LESS:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case GREATER_EQUAL:
				switch(operator2) {
				case LESS:
				case LESS_EQUAL:
					return new AbstractBooleanConstraint(true);
				case EQUAL:
				case GREATER:
				case GREATER_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case LESS:
				switch(operator2) {
				case GREATER_EQUAL:
					return new AbstractBooleanConstraint(true);
				case EQUAL:
				case GREATER:
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case LESS_EQUAL:
				switch(operator2) {
				case GREATER:
				case GREATER_EQUAL:
					return new AbstractBooleanConstraint(true);
				case EQUAL:
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			case NOT_EQUAL:
				switch(operator2) {
				case EQUAL:
					return new AbstractBooleanConstraint(true);
				case GREATER:
				case GREATER_EQUAL:
				case LESS:
				case LESS_EQUAL:
				case NOT_EQUAL:
					return this;
				default:
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.getAsciiName() + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			default:
				Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator1 == null ? "null" : "\"" + operator1.getAsciiName() + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator1);
			}
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.getCode() + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}
}
