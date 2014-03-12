package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.exceptions.UnsupportedConstraintLiteralNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;

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
		
		if(this.value1 instanceof AbstractConstraintLiteral && this.value2 instanceof AbstractConstraintLiteral) {
			AbstractConstraintLiteral<?> constraintLiteral1 = (AbstractConstraintLiteral<?>)this.value1;
			AbstractConstraintLiteral<?> constraintLiteral2 = (AbstractConstraintLiteral<?>)this.value2;

			if(constraintLiteral1.isNumberType && constraintLiteral2.isNumberType)
				return this.calculateLiterals(constraintLiteral1, this.operator, constraintLiteral2);
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
	 * 
	 * @param constraintLiteral1
	 * @param operator
	 * @param constraintLiteral2
	 * @return
	 */
	private AbstractConstraintLiteral<?> calculateLiterals(AbstractConstraintLiteral<?> constraintLiteral1, ArithmeticOperator operator, AbstractConstraintLiteral<?> constraintLiteral2) {
		/**  */
		if(constraintLiteral1 instanceof AbstractConstraintLiteralDouble) {
			if(constraintLiteral2 instanceof AbstractConstraintLiteralDouble)
				return new AbstractConstraintLiteralDouble(
						this.calculate(
								((AbstractConstraintLiteralDouble)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralDouble)constraintLiteral2).value));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralFloat)
				return new AbstractConstraintLiteralDouble(
						this.calculate(
								((AbstractConstraintLiteralDouble)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralFloat)constraintLiteral2).value.doubleValue()));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralInteger)
				return new AbstractConstraintLiteralDouble(
						this.calculate(
								((AbstractConstraintLiteralDouble)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralInteger)constraintLiteral2).value.doubleValue()));
			else {
				UnsupportedConstraintLiteralNumberTypeException e = new UnsupportedConstraintLiteralNumberTypeException(constraintLiteral2.getClass());
				Logger.getLogger(AbstractConstraintFormula.class).fatal(e.getMessage());
				throw e;
			}
		}
		/**  */
		else if(constraintLiteral1 instanceof AbstractConstraintLiteralFloat) {
			if(constraintLiteral2 instanceof AbstractConstraintLiteralDouble)
				return new AbstractConstraintLiteralDouble(
						this.calculate(
								((AbstractConstraintLiteralFloat)constraintLiteral1).value.doubleValue(),
								this.operator,
								((AbstractConstraintLiteralDouble)constraintLiteral2).value));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralFloat)
				return new AbstractConstraintLiteralFloat(
						this.calculate(
								((AbstractConstraintLiteralFloat)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralFloat)constraintLiteral2).value));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralInteger)
				return new AbstractConstraintLiteralFloat(
						this.calculate(
								((AbstractConstraintLiteralFloat)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralInteger)constraintLiteral2).value.floatValue()));
			else {
				UnsupportedConstraintLiteralNumberTypeException e = new UnsupportedConstraintLiteralNumberTypeException(constraintLiteral2.getClass());
				Logger.getLogger(AbstractConstraintFormula.class).fatal(e.getMessage());
				throw e;
			}
		}
		/**  */
		else if(constraintLiteral1 instanceof AbstractConstraintLiteralInteger) {
			if(constraintLiteral2 instanceof AbstractConstraintLiteralDouble)
				return new AbstractConstraintLiteralDouble(
						this.calculate(
								((AbstractConstraintLiteralInteger)constraintLiteral1).value.doubleValue(),
								this.operator,
								((AbstractConstraintLiteralDouble)constraintLiteral2).value));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralFloat)
				return new AbstractConstraintLiteralFloat(
						this.calculate(
								((AbstractConstraintLiteralInteger)constraintLiteral1).value.floatValue(),
								this.operator,
								((AbstractConstraintLiteralFloat)constraintLiteral2).value));
			if(constraintLiteral2 instanceof AbstractConstraintLiteralInteger)
				return new AbstractConstraintLiteralInteger(
						this.calculate(
								((AbstractConstraintLiteralInteger)constraintLiteral1).value,
								this.operator,
								((AbstractConstraintLiteralInteger)constraintLiteral2).value));
			else {
				UnsupportedConstraintLiteralNumberTypeException e = new UnsupportedConstraintLiteralNumberTypeException(constraintLiteral2.getClass());
				Logger.getLogger(AbstractConstraintFormula.class).fatal(e.getMessage());
				throw e;
			}
		}
		/**  */
		else {
			UnsupportedConstraintLiteralNumberTypeException e = new UnsupportedConstraintLiteralNumberTypeException(constraintLiteral1.getClass());
			Logger.getLogger(AbstractConstraintFormula.class).fatal(e.getMessage());
			throw e;
		}
	}
	
	/**
	 * calculate calculates the value of the two given doubles and returns the
	 *  calculation of those considering the given arithmetic operator.
	 * 
	 * @param value1 the first double
	 * @param operator the arithmetic operator
	 * @param value2 the second double
	 * 
	 * @return a new double for the calculation considering the arithmetic
	 *  operator
	 */
	private Double calculate(Double value1, ArithmeticOperator operator, Double value2) {
		switch(operator) {
		case ADD:
			return value1 + value2;
		case SUB:
			return value1 - value2;
		case MUL:
			return value1 * value2;
		case DIV:
			return value1 / value2;
		default:
			Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownArithmeticOperatorException(operator);
		}
	}
	
	/**
	 * calculate calculates the value of the two given floats and returns the
	 *  calculation of those considering the given arithmetic operator.
	 * 
	 * @param value1 the first float
	 * @param operator the arithmetic operator
	 * @param value2 the second float
	 * 
	 * @return a new float for the calculation considering the arithmetic
	 *  operator
	 */
	private Float calculate(Float value1, ArithmeticOperator operator, Float value2) {
		switch(operator) {
		case ADD:
			return value1 + value2;
		case SUB:
			return value1 - value2;
		case MUL:
			return value1 * value2;
		case DIV:
			return value1 / value2;
		default:
			Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownArithmeticOperatorException(operator);
		}
	}
	
	/**
	 * calculate calculates the value of the two given integers and returns the
	 *  calculation of those considering the given arithmetic operator.
	 * 
	 * @param value1 the first integer
	 * @param operator the arithmetic operator
	 * @param value2 the second integer
	 * 
	 * @return a new integer for the calculation considering the arithmetic
	 *  operator
	 */
	private Integer calculate(Integer value1, ArithmeticOperator operator, Integer value2) {
		switch(operator) {
		case ADD:
			return value1 + value2;
		case SUB:
			return value1 - value2;
		case MUL:
			return value1 * value2;
		case DIV:
			return value1 / value2;
		default:
			Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownArithmeticOperatorException(operator);
		}
	}
}
