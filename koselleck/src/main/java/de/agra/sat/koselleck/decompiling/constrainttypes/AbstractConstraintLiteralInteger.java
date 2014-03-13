package de.agra.sat.koselleck.decompiling.constrainttypes;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralInteger extends AbstractConstraintLiteral<Integer> {
	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralInteger(Integer value) {
		super(value, false, false, true);
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
		if(!(object instanceof AbstractConstraintLiteralInteger))
			return false;
		
		AbstractConstraintLiteralInteger abstractConstraintLiteralInteger = (AbstractConstraintLiteralInteger)object;
		
		return this.value.equals(abstractConstraintLiteralInteger.value) &&
				this.isVariable == abstractConstraintLiteralInteger.isVariable;
	}

	@Override
	public AbstractConstraintLiteral<Integer> clone() {
		return new AbstractConstraintLiteralInteger(this.value);
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
			return ((Float) this.value.floatValue()).compareTo((Float) constraintLiteral.value);
		else if (constraintLiteral.value instanceof Integer)
			return this.value.compareTo((Integer) constraintLiteral.value);
		else {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintLiteralClass.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintLiteral<?> add(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.value instanceof Double)
			return new AbstractConstraintLiteralDouble(this.value.doubleValue() + ((Double) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Float)
			return new AbstractConstraintLiteralFloat(this.value.floatValue() + ((Float) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Integer)
			return new AbstractConstraintLiteralInteger(this.value + ((Integer) constraintLiteral.value));
		else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintLiteral<?> sub(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.value instanceof Double)
			return new AbstractConstraintLiteralDouble(this.value.doubleValue() - ((Double) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Float)
			return new AbstractConstraintLiteralFloat(this.value.floatValue() - ((Float) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Integer)
			return new AbstractConstraintLiteralInteger(this.value - ((Integer) constraintLiteral.value));
		else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintLiteral<?> mul(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.value instanceof Double)
			return new AbstractConstraintLiteralDouble(this.value.doubleValue() * ((Double) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Float)
			return new AbstractConstraintLiteralFloat(this.value.floatValue() * ((Float) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Integer)
			return new AbstractConstraintLiteralInteger(this.value * ((Integer) constraintLiteral.value));
		else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintLiteral<?> div(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (constraintLiteral.value instanceof Double)
			return new AbstractConstraintLiteralDouble(this.value.doubleValue() / ((Double) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Float)
			return new AbstractConstraintLiteralFloat(this.value.floatValue() / ((Float) constraintLiteral.value));
		else if (constraintLiteral.value instanceof Integer)
			return new AbstractConstraintLiteralInteger(this.value / ((Integer) constraintLiteral.value));
		else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
