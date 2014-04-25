package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralDouble extends AbstractConstraintLiteral<Double> {
	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralDouble(Double value) {
		super(value, false, true, true);
	}

	@Override
	public void replaceAll(String regex, String replacement) {}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public boolean matches(String regex) {
		return false;
	}

	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractConstraintLiteralDouble))
			return false;
		
		AbstractConstraintLiteralDouble abstractConstraintLiteralDouble = (AbstractConstraintLiteralDouble)object;
		
		return this.value.equals(abstractConstraintLiteralDouble.value) &&
				this.isVariable == abstractConstraintLiteralDouble.isVariable;
	}

	@Override
	public AbstractConstraintLiteralDouble clone() {
		return new AbstractConstraintLiteralDouble(this.value);
	}

	@Override
	public String toString() {
		return this.value.toString();
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (constraintLiteral.value instanceof Double)
			return this.value.compareTo((Double) constraintLiteral.value);
		else if (constraintLiteral.value instanceof Float)
			return this.value.compareTo(((Float) constraintLiteral.value).doubleValue());
		else if (constraintLiteral.value instanceof Integer)
			return this.value.compareTo(((Integer) constraintLiteral.value).doubleValue());
		else {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintLiteralClass.class).fatal(exception.getMessage());
			throw exception;
		}
	}
	
	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.value instanceof Double) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.value + ((Double) constraintLiteral.value));
			case SUB:
				return new AbstractConstraintLiteralDouble(this.value - ((Double) constraintLiteral.value));
			case MUL:
				return new AbstractConstraintLiteralDouble(this.value * ((Double) constraintLiteral.value));
			case DIV:
				return new AbstractConstraintLiteralDouble(this.value / ((Double) constraintLiteral.value));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.value instanceof Float) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.value + ((Float) constraintLiteral.value).doubleValue());
			case SUB:
				return new AbstractConstraintLiteralDouble(this.value - ((Float) constraintLiteral.value).doubleValue());
			case MUL:
				return new AbstractConstraintLiteralDouble(this.value * ((Float) constraintLiteral.value).doubleValue());
			case DIV:
				return new AbstractConstraintLiteralDouble(this.value / ((Float) constraintLiteral.value).doubleValue());
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.value instanceof Integer) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.value + ((Integer) constraintLiteral.value).doubleValue());
			case SUB:
				return new AbstractConstraintLiteralDouble(this.value - ((Integer) constraintLiteral.value).doubleValue());
			case MUL:
				return new AbstractConstraintLiteralDouble(this.value * ((Integer) constraintLiteral.value).doubleValue());
			case DIV:
				return new AbstractConstraintLiteralDouble(this.value / ((Integer) constraintLiteral.value).doubleValue());
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
