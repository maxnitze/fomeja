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
		super(value, null, false, true, true);
	}

	/**
	 * 
	 * @param name
	 */
	public AbstractConstraintLiteralFloat(String name) {
		super(null, name, true, true, true);
	}

	/** inherited methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {}

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

		return this.getValue().equals(abstractConstraintLiteralFloat.getValue()) &&
				this.isVariable() == abstractConstraintLiteralFloat.isVariable();
	}

	@Override
	public AbstractConstraintLiteralFloat clone() {
		return new AbstractConstraintLiteralFloat(this.getValue());
	}

	@Override
	public String toString() {
		return this.getValue().toString();
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (constraintLiteral.getValue() instanceof Double)
			return ((Double) this.getValue().doubleValue()).compareTo((Double) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Float)
			return this.getValue().compareTo((Float) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Integer)
			return this.getValue().compareTo(((Integer) constraintLiteral.getValue()).floatValue());
		else {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintLiteralClass.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.getValue() instanceof Double) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.getValue().doubleValue() + ((Double) constraintLiteral.getValue()));
			case SUB:
				return new AbstractConstraintLiteralDouble(this.getValue().doubleValue() - ((Double) constraintLiteral.getValue()));
			case MUL:
				return new AbstractConstraintLiteralDouble(this.getValue().doubleValue() * ((Double) constraintLiteral.getValue()));
			case DIV:
				return new AbstractConstraintLiteralDouble(this.getValue().doubleValue() / ((Double) constraintLiteral.getValue()));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.getValue() instanceof Float) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralFloat(this.getValue() + ((Float) constraintLiteral.getValue()));
			case SUB:
				return new AbstractConstraintLiteralFloat(this.getValue() - ((Float) constraintLiteral.getValue()));
			case MUL:
				return new AbstractConstraintLiteralFloat(this.getValue() * ((Float) constraintLiteral.getValue()));
			case DIV:
				return new AbstractConstraintLiteralFloat(this.getValue() / ((Float) constraintLiteral.getValue()));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.getValue() instanceof Integer) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralFloat(this.getValue() + ((Integer) constraintLiteral.getValue()).floatValue());
			case SUB:
				return new AbstractConstraintLiteralFloat(this.getValue() - ((Integer) constraintLiteral.getValue()).floatValue());
			case MUL:
				return new AbstractConstraintLiteralFloat(this.getValue() * ((Integer) constraintLiteral.getValue()).floatValue());
			case DIV:
				return new AbstractConstraintLiteralFloat(this.getValue() / ((Integer) constraintLiteral.getValue()).floatValue());
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
