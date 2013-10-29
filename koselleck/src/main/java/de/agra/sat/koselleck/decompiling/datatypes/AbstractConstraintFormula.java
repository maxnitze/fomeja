package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnsupportedNumberTypeException;

/**
 * AbstractConstraintFormula represents a formula in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class AbstractConstraintFormula extends AbstractConstraintValue {
	/** the first value */
	public AbstractConstraintValue value1;
	/** the arithmetic operator */
	public final ArithmeticOperator operator;
	/** the second value */
	public AbstractConstraintValue value2;
	
	/**
	 * Constructor for a new AbstractConstraintFormula.
	 * 
	 * @param value1 the new first value
	 * @param operator the new arithmetic operator
	 * @param value2 the new second value
	 */
	public AbstractConstraintFormula(AbstractConstraintValue value1, ArithmeticOperator operator, AbstractConstraintValue value2) {
		this.value1 = value1;
		this.operator = operator;
		this.value2 = value2;
	}
	
	/**
	 * replaceAll replaces all occurrences of the regular expression
	 *  {@code regex} of the values with the given {@code replacement} by
	 *  calling the replaceAll(String, String) method of the values.
	 * 
	 * @param regex the regular expression to look for
	 * @param replacement the string to replace the matches with
	 */
	@Override
	public void replaceAll(String regex, String replacement) {
		this.value1.replaceAll(regex, replacement);
		this.value2.replaceAll(regex, replacement);
	}
	
	/**
	 * replaceAll replaces all occurrences of the given prefixed field
	 *  {@code prefixedField} of the values with the given {@code replacement}
	 *  by calling the replaceAll(PrefixedField, String) method of the values.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * @param replacement the string to replace the matches with
	 */
	@Override
	public void replaceAll(PrefixedField prefixedField, String replacement) {
		this.value1.replaceAll(prefixedField, replacement);
		this.value2.replaceAll(prefixedField, replacement);
	}
	
	/**
	 * evaluate first evaluates both values by calling their evaluate method. 
	 *  Afterwards a new abstract constraint literal with the calculated value
	 *  of the values is returned if both are of type integer. Otherwise this
	 *  current object is returned.
	 * 
	 * @return a new abstract constraint literal if both values are of type
	 *  integer, this object otherwise
	 */
	@Override
	public AbstractConstraintValue evaluate() {
		this.value1 = this.value1.evaluate();
		this.value2 = this.value2.evaluate();
		
		if(
				this.value1 instanceof AbstractConstraintLiteral &&
				this.value2 instanceof AbstractConstraintLiteral) {
			AbstractConstraintLiteral constraintLiteral1 = (AbstractConstraintLiteral)this.value1;
			AbstractConstraintLiteral constraintLiteral2 = (AbstractConstraintLiteral)this.value2;
			if(
					constraintLiteral1.valueType == ConstraintValueType.INTEGER &&
					constraintLiteral2.valueType == ConstraintValueType.INTEGER)
				return new AbstractConstraintLiteral(
						calculateValue(
								(Integer)constraintLiteral1.value,
								this.operator,
								(Integer)constraintLiteral2.value),
						ConstraintValueType.INTEGER,
						false);
			else
				return this;
		} else
			return this;
	}
	
	/**
	 * matches checks if this object matches the given regular expression
	 *  {@code regex} by calling the matches(String) method of both values.
	 * 
	 * @param regex the regular expression to look for
	 * 
	 * @return {@code true} if one of the values matches the given regular
	 *  expression, {@code false} otherwise
	 */
	@Override
	public boolean matches(String regex) {
		return this.value1.matches(regex) || this.value2.matches(regex);
	}
	
	/**
	 * matches checks if this object matches the given prefixed field
	 *  {@code prefixedField} by calling the matches(String) method of both
	 *  values.
	 * 
	 * @param prefixedField the prefixed field to look for
	 * 
	 * @return {@code true} if one of the values matches the given prefixed
	 *  field, {@code false} otherwise
	 */
	@Override
	public boolean matches(PrefixedField prefixedField) {
		return this.value1.matches(prefixedField) || this.value2.matches(prefixedField);
	}
	
	/**
	 * equals checks if this abstract constraint formula and the given object
	 *  are equal.
	 * 
	 * @param object the object to check for equality
	 * 
	 * @return {@code true} if the given object an this abstract constraint
	 *  formula are equal, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractConstraintFormula))
			return false;
		
		AbstractConstraintFormula constraintFormula = (AbstractConstraintFormula)object;
		
		return
				this.value1.equals(constraintFormula.value1) &&
				this.operator == constraintFormula.operator &&
				this.value2.equals(constraintFormula.value2);
	}
	
	/**
	 * clone returns a copy of this abstract constraint formula.
	 * 
	 * @return a copy of this abstract constraint formula
	 */
	@Override
	public AbstractConstraintValue clone() {
		return new AbstractConstraintFormula(
				this.value1.clone(),
				this.operator,
				this.value2.clone());
	}
	
	/**
	 * toString returns the string representation of this abstract constraint
	 *  formula.
	 * 
	 * @return the string representation of this abstract constraint formula
	 */
	@Override
	public String toString() {
		StringBuilder stringRepresentation = new StringBuilder();
		stringRepresentation.append("(");
		stringRepresentation.append(this.value1.toString());
		stringRepresentation.append(this.operator.asciiName);
		stringRepresentation.append(this.value2.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * calculateValue calculates the value of the two given numbers and returns
	 *  the calculation of those considering the given arithmetic operator.
	 * 
	 * @param value1 the first number
	 * @param operator the arithmetic operator
	 * @param value2 the second number
	 * 
	 * @return a new number for the calculation considering the arithmetic
	 *  operator
	 */
	private <T extends Number, U extends Number> Number calculateValue(T value1, ArithmeticOperator operator, U value2) {
		switch(operator) {
		case ADD:
			if(value1 instanceof Integer) {
				if(value2 instanceof Integer)
					return new Integer(value1.intValue() + value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.intValue() + value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.intValue() + value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Double) {
				if(value2 instanceof Integer)
					return new Double(value1.doubleValue() + value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.doubleValue() + value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.doubleValue() + value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Float) {
				if(value2 instanceof Integer)
					return new Float(value1.floatValue() + value2.intValue());
				else if(value2 instanceof Double)
					return new Float(value1.floatValue() + value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.floatValue() + value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else {
				Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value1 == null ? "null" : value1.getClass().getSimpleName()) + "\" is not supported");
				throw new UnsupportedNumberTypeException(value1);
			}
		case SUB:
			if(value1 instanceof Integer) {
				if(value2 instanceof Integer)
					return new Integer(value1.intValue() - value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.intValue() - value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.intValue() - value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Double) {
				if(value2 instanceof Integer)
					return new Double(value1.doubleValue() - value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.doubleValue() - value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.doubleValue() - value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Float) {
				if(value2 instanceof Integer)
					return new Float(value1.floatValue() - value2.intValue());
				else if(value2 instanceof Double)
					return new Float(value1.floatValue() - value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.floatValue() - value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else {
				Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value1 == null ? "null" : value1.getClass().getSimpleName()) + "\" is not supported");
				throw new UnsupportedNumberTypeException(value1);
			}
		case MUL:
			if(value1 instanceof Integer) {
				if(value2 instanceof Integer)
					return new Integer(value1.intValue() * value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.intValue() * value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.intValue() * value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Double) {
				if(value2 instanceof Integer)
					return new Double(value1.doubleValue() * value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.doubleValue() * value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.doubleValue() * value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Float) {
				if(value2 instanceof Integer)
					return new Float(value1.floatValue() * value2.intValue());
				else if(value2 instanceof Double)
					return new Float(value1.floatValue() * value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.floatValue() * value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else {
				Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value1 == null ? "null" : value1.getClass().getSimpleName()) + "\" is not supported");
				throw new UnsupportedNumberTypeException(value1);
			}
		case DIV:
			if(value1 instanceof Integer) {
				if(value2 instanceof Integer)
					return new Integer(value1.intValue() / value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.intValue() / value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.intValue() / value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Double) {
				if(value2 instanceof Integer)
					return new Double(value1.doubleValue() / value2.intValue());
				else if(value2 instanceof Double)
					return new Double(value1.doubleValue() / value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.doubleValue() / value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else if(value1 instanceof Float) {
				if(value2 instanceof Integer)
					return new Float(value1.floatValue() / value2.intValue());
				else if(value2 instanceof Double)
					return new Float(value1.floatValue() / value2.doubleValue());
				else if(value2 instanceof Float)
					return new Float(value1.floatValue() / value2.floatValue());
				else {
					Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value2 == null ? "null" : value2.getClass().getSimpleName()) + "\" is not supported");
					throw new UnsupportedNumberTypeException(value2);
				}
			} else {
				Logger.getLogger(AbstractConstraintFormula.class).fatal("number type \"" + (value1 == null ? "null" : value1.getClass().getSimpleName()) + "\" is not supported");
				throw new UnsupportedNumberTypeException(value1);
			}
		default:
			Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownArithmeticOperatorException(operator);
		}
	}
}
