package de.agra.sat.koselleck.decompiling.datatypes;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;

/**
 * 
 * @author Max Nitze
 */
public class AbstractSingleConstraint extends AbstractConstraint {
	/**  */
	public AbstractConstraintValue value1;
	/**  */
	public final ConstraintOperator operator;
	/**  */
	public AbstractConstraintValue value2;
	
	/**
	 * 
	 * @param value1
	 * @param operator
	 * @param value2
	 */
	public AbstractSingleConstraint(AbstractConstraintValue value1, ConstraintOperator operator, AbstractConstraintValue value2, List<PrefixedField> prefixedFields) {
		this.prefixedFields.addAll(prefixedFields);
		
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}
	
	/**
	 * 
	 * @param regex
	 * @param replacement
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * @param replacement
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.value1.replaceAll(prefixedField, replacement);
		this.value2.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * 
	 * @return
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
	 * 
	 * @param regex
	 * 
	 * @return
	 */
	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}
	
	/**
	 * 
	 * @param prefixedField
	 * 
	 * @return
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.value1.matches(prefixedField) || this.value2.matches(prefixedField);
	}
	
	/**
	 * 
	 * @param obj
	 * 
	 * @return
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
	 * 
	 * @return
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
	 * 
	 * @return
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
	 * 
	 * @param value1
	 * @param value2
	 * 
	 * @return
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
