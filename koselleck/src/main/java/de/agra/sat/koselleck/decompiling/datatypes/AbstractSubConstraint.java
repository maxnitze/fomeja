package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;

/**
 * 
 * @author Max Nitze
 */
public class AbstractSubConstraint extends AbstractConstraint {
	/**  */
	public AbstractConstraint constraint1;
	/**  */
	public final BooleanConnector connector;
	/**  */
	public AbstractConstraint constraint2;
	
	/**
	 * 
	 * @param constraint1
	 * @param connector
	 * @param constraint2
	 */
	public AbstractSubConstraint(AbstractConstraint constraint1, BooleanConnector connector, AbstractConstraint constraint2) {
		this.prefixedFields.addAll(constraint1.prefixedFields);
		this.prefixedFields.addAll(constraint2.prefixedFields);
		
		this.constraint1 = constraint1;
		this.connector = connector;
		this.constraint2 = constraint2;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.constraint1.replaceAll(regex, replacement);
		this.constraint2.replaceAll(regex, replacement);
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.constraint1.replaceAll(prefixedField, replacement);
		this.constraint2.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.constraint1 = this.constraint1.evaluate();
		this.constraint2 = this.constraint2.evaluate();
		
		/** evaluate to boolean if both sub-constraints are boolean
		 * constraints */
		if(
				this.constraint1 instanceof AbstractBooleanConstraint &&
				this.constraint2 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
						((AbstractBooleanConstraint)this.constraint1).value,
						((AbstractBooleanConstraint)this.constraint2).value);
		/** evaluate constraint if the first sub-constraints is a boolean
		 * constraint */
		else if(this.constraint1 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
					((AbstractBooleanConstraint)this.constraint1).value,
					this.constraint2);
		/** evaluate constraint if the second sub-constraints is a boolean
		 * constraint */
		else if(this.constraint2 instanceof AbstractBooleanConstraint)
			return evaluateConstraint(
					((AbstractBooleanConstraint)this.constraint2).value,
					this.constraint1);
		/** try to evaluate constraint if both sub-constraints are single
		 * constraints */
		else if(
				this.constraint1 instanceof AbstractSingleConstraint &&
				this.constraint2 instanceof AbstractSingleConstraint) {
			AbstractSingleConstraint singleConstraint1 = (AbstractSingleConstraint)this.constraint1;
			AbstractSingleConstraint singleConstraint2 = (AbstractSingleConstraint)this.constraint2;
			
			/** evaluate to one constraint if both constraints are equal */
			if(singleConstraint1.equals(singleConstraint2))
				return singleConstraint1;
			/** evaluate the constraint if the values of both sub-constraints
			 * are equal */
			else if(
					singleConstraint1.value1.equals(singleConstraint2.value1) &&
					singleConstraint1.value2.equals(singleConstraint2.value2))
				return evaluateEqualConstraints(
						singleConstraint1.operator,
						singleConstraint2.operator);
			/** evaluate the constraint if the values of both sub-constraints
			 * are equal */
			else if(
					singleConstraint1.value1.equals(singleConstraint2.value2) &&
					singleConstraint1.value2.equals(singleConstraint2.value1))
				return evaluateEqualConstraints(
						singleConstraint1.operator,
						ConstraintOperator.fromSwappedAsciiName(singleConstraint2.operator.asciiName));
			else
				return this;
		} else
			return this;
	}
	
	/**
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	@Override
	public boolean matches(String regex) {
		return this.constraint1.matches(regex) || this.constraint2.matches(regex);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.constraint1.matches(prefixedField) || this.constraint2.matches(prefixedField);
	}
	
	/**
	 * 
	 * @param obj
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AbstractSubConstraint))
			return false;
		
		AbstractSubConstraint subConstraint = (AbstractSubConstraint)obj;
		
		return
				this.constraint1.equals(subConstraint.constraint1) &&
				this.connector == subConstraint.connector &&
				this.constraint2.equals(subConstraint.constraint2);
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraint clone() {
		List<PrefixedField> prefixedFields = new ArrayList<PrefixedField>();
		prefixedFields.addAll(this.prefixedFields);
		return new AbstractSubConstraint(
				this.constraint1.clone(),
				this.connector,
				this.constraint2.clone());
	}
	
	/**
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("(");
		stringRepresentation.append(this.constraint1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.connector.code);
		stringRepresentation.append(" ");
		stringRepresentation.append(this.constraint2.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param value1
	 * @param value2
	 * 
	 * @return
	 */
	private AbstractConstraint evaluateConstraint(boolean value1, boolean value2) {
		switch(this.connector) {
		case AND:
			return new AbstractBooleanConstraint(value1 && value2);
		case OR:
			return new AbstractBooleanConstraint(value1 || value2);
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.code + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}
	
	/**
	 * 
	 * @param booleanValue
	 * @param constraintValue
	 * 
	 * @return
	 */
	private AbstractConstraint evaluateConstraint(boolean booleanValue, AbstractConstraint constraintValue) {
		switch(this.connector) {
		case AND:
			if(booleanValue)
				return constraintValue;
			else
				return new AbstractBooleanConstraint(false);
		case OR:
			if(booleanValue)
				return new AbstractBooleanConstraint(true);
			else
				return constraintValue;
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.code + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}
	
	/**
	 * 
	 * @param operator1
	 * @param operator2
	 * 
	 * @return
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			default:
				Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator1 == null ? "null" : "\"" + operator1.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
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
					Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator2 == null ? "null" : "\"" + operator2.asciiName + "\"") + " is not known");
					throw new UnknownConstraintOperatorException(operator2);
				}
			default:
				Logger.getLogger(AbstractSubConstraint.class).fatal("constraint operator " + (operator1 == null ? "null" : "\"" + operator1.asciiName + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(operator1);
			}
		default:
			Logger.getLogger(AbstractSubConstraint.class).fatal("boolean connector " + (this.connector == null ? "null" : "\"" + this.connector.code + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(this.connector);
		}
	}
}
