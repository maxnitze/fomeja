package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralString extends AbstractConstraintLiteral<String> {
	/**  */
	public final Class<?> type;

	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralString(String value, Class<?> type) {
		super(value, true, false, false);
		this.type = type;
	}

	@Override
	public void replaceAll(String regex, String replacement) {
		this.value.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		if (this.value.matches("^\\d+(\\.\\d+)?d$"))
			return new AbstractConstraintLiteralDouble(Double.parseDouble(this.value));
		else if (this.value.matches("^\\d+(\\.\\d+)?f$"))
			return new AbstractConstraintLiteralFloat(Float.parseFloat(this.value));
		else if (this.value.matches("^\\d+$"))
			return new AbstractConstraintLiteralInteger(Integer.parseInt(this.value));
		else
			return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		return this;
	}

	@Override
	public boolean matches(String regex) {
		return this.value.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractConstraintLiteralString))
			return false;

		AbstractConstraintLiteralString abstractConstraintLiteralString = (AbstractConstraintLiteralString)object;

		return this.value.equals(abstractConstraintLiteralString.value);
	}

	@Override
	public AbstractConstraintLiteralString clone() {
		return new AbstractConstraintLiteralString(this.value, this.type);
	}

	@Override
	public String toString() {
		return this.value;
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralString.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralString.class).fatal(exception.getMessage());
		throw exception;
	}
}
