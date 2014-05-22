package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralFloat extends AbstractConstraintLiteral<Float> {
	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralFloat(Float value) {
		super(value, false, true, true);
	}

	@Override
	public void replaceAll(String regex, String replacement) {}

	@Override
	public void changeStringLiteralType(String regex, Class<?> type) {}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		return this;
	}

	@Override
	public boolean matches(String regex) {
		return false;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintLiteralFloat))
			return false;

		AbstractConstraintLiteralFloat abstractConstraintLiteralFloat = (AbstractConstraintLiteralFloat)object;

		return this.value.equals(abstractConstraintLiteralFloat.value) &&
				this.isVariable == abstractConstraintLiteralFloat.isVariable;
	}

	@Override
	public AbstractConstraintLiteralFloat clone() {
		return new AbstractConstraintLiteralFloat(this.value);
	}

	@Override
	public String toString() {
		return this.value.toString();
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (constraintLiteral.value instanceof Double)
			return ((Double) this.value.doubleValue()).compareTo((Double) constraintLiteral.value);
		else if (constraintLiteral.value instanceof Float)
			return this.value.compareTo((Float) constraintLiteral.value);
		else if (constraintLiteral.value instanceof Integer)
			return this.value.compareTo(((Integer) constraintLiteral.value).floatValue());
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
				return new AbstractConstraintLiteralDouble(this.value.doubleValue() + ((Double) constraintLiteral.value));
			case SUB:
				return new AbstractConstraintLiteralDouble(this.value.doubleValue() - ((Double) constraintLiteral.value));
			case MUL:
				return new AbstractConstraintLiteralDouble(this.value.doubleValue() * ((Double) constraintLiteral.value));
			case DIV:
				return new AbstractConstraintLiteralDouble(this.value.doubleValue() / ((Double) constraintLiteral.value));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.value instanceof Float) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralFloat(this.value + ((Float) constraintLiteral.value));
			case SUB:
				return new AbstractConstraintLiteralFloat(this.value - ((Float) constraintLiteral.value));
			case MUL:
				return new AbstractConstraintLiteralFloat(this.value * ((Float) constraintLiteral.value));
			case DIV:
				return new AbstractConstraintLiteralFloat(this.value / ((Float) constraintLiteral.value));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.value instanceof Integer) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralFloat(this.value + ((Integer) constraintLiteral.value).floatValue());
			case SUB:
				return new AbstractConstraintLiteralFloat(this.value - ((Integer) constraintLiteral.value).floatValue());
			case MUL:
				return new AbstractConstraintLiteralFloat(this.value * ((Integer) constraintLiteral.value).floatValue());
			case DIV:
				return new AbstractConstraintLiteralFloat(this.value / ((Integer) constraintLiteral.value).floatValue());
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
