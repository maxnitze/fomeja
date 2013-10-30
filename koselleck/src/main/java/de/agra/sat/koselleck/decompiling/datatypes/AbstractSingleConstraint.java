package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;

/**
 * AbstractSingleConstraint represents a single constraint in a constraint.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractSingleConstraint extends AbstractConstraint {
	/** the first value */
	public AbstractConstraintValue value1;
	/** the constraint operator */
	public final ConstraintOperator operator;
	/** the second value */
	public AbstractConstraintValue value2;
	
	/**
	 * Constructor for a new abstract single constraint.
	 * 
	 * @param value1 the new first value
	 * @param operator the new constraint operator
	 * @param value2 the new second value
	 */
	public AbstractSingleConstraint(AbstractConstraintValue value1, ConstraintOperator operator, AbstractConstraintValue value2, List<PrefixedField> prefixedFields) {
		this.prefixedFields.addAll(prefixedFields);
		
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}
	
	/**
	 * replaceAll replaces all occurrences of the given regular expression
	 *  {@code regex} with the given replacement {@code replacement} by calling
	 *  the replaceAll(String, String) method of the two values.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the replacement
	 * 
	 * @see AbstractConstraintValue#replaceAll(String, String)
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}
	
	/**
	 * replaceAll replaces all occurrences of the given prefixed field
	 *  {@code prefixedField} with the given replacement {@code replacement} by
	 *  calling the replaceAll(PrefixedField, String) method of the two values.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * @param replacement the replacement
	 * 
	 * @see AbstractConstraintValue#replaceAll(PrefixedField, String)
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.value1.replaceAll(prefixedField, replacement);
		this.value2.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * evaluate evaluates this abstract single constraint. At first both values
	 *  are evaluated. If these new values are of type integer afterwards the
	 *  boolean value of this single constraint is calculated. If the values
	 *  are both strings/variables and they are equal the boolean value of
	 *  this single constraint is calculated. Otherwise this abstract single
	 *  constraint is returned.
	 * 
	 * @return the boolean value of this single constraint if possible to
	 *  calculate, this abstract single constraint otherwise
	 */
	@Override
	public AbstractConstraint evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();
		
		if(
				!(this.value1 instanceof AbstractConstraintLiteral) ||
				!(this.value2 instanceof AbstractConstraintLiteral))
			return this;
		
		AbstractConstraintLiteral constraintLiteral1 = (AbstractConstraintLiteral)this.value1;
		AbstractConstraintLiteral constraintLiteral2 = (AbstractConstraintLiteral)this.value2;
		
		/** evaluate to boolean if both values are integer */
		if(
				constraintLiteral1.valueType == ConstraintValueType.INTEGER &&
				constraintLiteral2.valueType == ConstraintValueType.INTEGER)
			return evaluateConstraint(
						(Integer)constraintLiteral1.value,
						(Integer)constraintLiteral2.value);
		/** evaluate to boolean if both values are equal strings */
		else if(
				constraintLiteral1.valueType == ConstraintValueType.STRING &&
				constraintLiteral2.valueType == ConstraintValueType.STRING &&
				((String)constraintLiteral1.value).equals((String)constraintLiteral2.value)) {
			switch(this.operator) {
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
				Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (this.operator == null ? "null" : "\"" + this.operator.asciiName + "\"") + " is not known");
				throw new UnknownConstraintOperatorException(this.operator);
			}
		} else
			return this;
	}
	
	/**
	 * matches checks if one or both of the values match the given regular
	 *  expression {@code regex}.
	 * 
	 * @param regex the regular expression to look for
	 * 
	 * @return {@code true} if one or both of the values match the given
	 *  regular expression {@code regex}, {@code false} otherwise
	 */
	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}
	
	/**
	 * matches checks if one or both of the values match the given prefixed
	 *  field {@code prefixedField}.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * 
	 * @return {@code true} if one or both of the values match the given
	 *  prefixed field {@code prefixedField}, {@code false} otherwise
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.value1.matches(prefixedField) || this.value2.matches(prefixedField);
	}
	
	/**
	 * equals checks if this abstract single constraint and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object matches this abstract
	 *  single constraint, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof AbstractSingleConstraint))
			return false;
		
		AbstractSingleConstraint singleConstraint = (AbstractSingleConstraint)obj;
		
		return (
				(this.value1.equals(singleConstraint.value1) &&
						this.value2.equals(singleConstraint.value2) &&
						(this.operator == singleConstraint.operator)) ||
				(this.value1.equals(singleConstraint.value2) &&
						this.value2.equals(singleConstraint.value1) &&
						(this.operator == ConstraintOperator.fromSwappedAsciiName(singleConstraint.operator.opcode))));
	}
	
	/**
	 * clone returns a copy of this abstract single constraint.
	 * 
	 * @return a copy of this abstract single constraint
	 */
	@Override
	public AbstractConstraint clone() {
		List<PrefixedField> prefixedFields = new ArrayList<PrefixedField>();
		prefixedFields.addAll(this.prefixedFields);
		return new AbstractSingleConstraint(
				this.value1.clone(),
				this.operator,
				this.value2.clone(),
				prefixedFields);
	}
	
	/**
	 * toString returns the string representation of this abstract single
	 *  constraint.
	 * 
	 * @return the string representation of this abstract single constraint
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("(");
		stringRepresentation.append(this.value1.toString());
		stringRepresentation.append(" ");
		stringRepresentation.append(this.operator.asciiName);
		stringRepresentation.append(" ");
		stringRepresentation.append(this.value2.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * evaluateConstraint evaluates the given comparable values to its abstract
	 *  boolean value considering the operator.
	 * 
	 * @param value1 the first comparable value
	 * @param value2 the second comparable value
	 * 
	 * @return the abstract boolean value of the given comparable values
	 *  considering the operator
	 */
	private <T extends Comparable<T>> AbstractBooleanConstraint evaluateConstraint(T value1, T value2) {
		switch(this.operator) {
		case EQUAL:
			return new AbstractBooleanConstraint(value1.compareTo(value2) == 0);
		case GREATER:
			return new AbstractBooleanConstraint(value1.compareTo(value2) > 0);
		case GREATER_EQUAL:
			return new AbstractBooleanConstraint(value1.compareTo(value2) >= 0);
		case LESS:
			return new AbstractBooleanConstraint(value1.compareTo(value2) < 0);
		case LESS_EQUAL:
			return new AbstractBooleanConstraint(value1.compareTo(value2) <= 0);
		case NOT_EQUAL:
			return new AbstractBooleanConstraint(value1.compareTo(value2) != 0);
		default:
			Logger.getLogger(AbstractSingleConstraint.class).fatal("constraint operator " + (this.operator == null ? "null" : "\"" + this.operator.asciiName + "\"") + " is not known");
			throw new UnknownConstraintOperatorException(this.operator);
		}
	}
}
