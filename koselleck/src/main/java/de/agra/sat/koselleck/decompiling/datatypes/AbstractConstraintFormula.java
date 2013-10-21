package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnsupportedNumberTypeException;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintFormula extends AbstractConstraintValue {
	/**  */
	public AbstractConstraintValue value1;
	/**  */
	public final ArithmeticOperator operator;
	/**  */
	public AbstractConstraintValue value2;
	
	/**
	 * 
	 * @param value1
	 * @param operator
	 * @param value2
	 */
	public AbstractConstraintFormula(AbstractConstraintValue value1, ArithmeticOperator operator, AbstractConstraintValue value2) {
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
	 * @param object
	 * 
	 * @return
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
	 * 
	 * @return
	 */
	@Override
	public AbstractConstraintValue clone() {
		return new AbstractConstraintFormula(
				this.value1.clone(),
				this.operator,
				this.value2.clone());
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
		stringRepresentation.append(this.operator.asciiName);
		stringRepresentation.append(this.value2.toString());
		stringRepresentation.append(")");
		return stringRepresentation.toString();
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param value1
	 * @param operator
	 * @param value2
	 * 
	 * @return
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
