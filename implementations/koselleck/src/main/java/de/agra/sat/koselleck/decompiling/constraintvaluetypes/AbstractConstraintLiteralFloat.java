package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

import java.lang.reflect.Field;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.exceptions.UnknownArithmeticOperatorException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.Opcode;

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
		super(value, true, true);
	}

	/**
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 */
	public AbstractConstraintLiteralFloat(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, true, false);
	}

	/**
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralFloat(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex, List<PreField> preFields) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, true, false, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AbstractConstraintLiteralFloat(String name) {
		super(name, true, false);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		if (!this.isFinishedType() && this.getName().matches(regex)) {
			if (replacement.matches("^\\d+(\\.\\d+)?d$"))
				this.setValueAndFinish(((Double) Double.parseDouble(replacement)).floatValue());
			else if (replacement.matches("^\\d+(\\.\\d+)?f$"))
				this.setValueAndFinish(Float.parseFloat(replacement));
			else if (replacement.matches("^\\d+$"))
				this.setValueAndFinish(((Integer) Integer.parseInt(replacement)).floatValue());
			else 
				this.setName(replacement);
		}
	}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintLiteralFloat))
			return false;

		AbstractConstraintLiteralFloat abstractConstraintLiteralFloat = (AbstractConstraintLiteralFloat)object;

		if (this.isFinishedType())
			return this.getValue().equals(abstractConstraintLiteralFloat.getValue());
		else
			return this.getField().equals(abstractConstraintLiteralFloat.getField())
					&& this.getName().equals(abstractConstraintLiteralFloat.getName())
					&& this.getFieldCodeIndex() == abstractConstraintLiteralFloat.getFieldCodeIndex()
					&& this.getOpcode().equals(abstractConstraintLiteralFloat.getOpcode())
					&& this.getConstantTableIndex() == abstractConstraintLiteralFloat.getConstantTableIndex();
	}

	@Override
	public AbstractConstraintLiteralFloat clone() {
		if (this.isFinishedType())
			return new AbstractConstraintLiteralFloat(this.getValue());
		else
			return new AbstractConstraintLiteralFloat(this.getField(), this.getFieldCodeIndex(), this.getOpcode(), this.getConstantTableIndex(), this.getPreFieldList());
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (this.isFinishedType() || !constraintLiteral.isFinishedNumberType()) {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintClass.class).fatal(exception.getMessage());
			throw exception;
		} else if (constraintLiteral.getValue() instanceof Double)
			return ((Double) this.getValue().doubleValue()).compareTo((Double) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Float)
			return this.getValue().compareTo((Float) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Integer)
			return this.getValue().compareTo(((Integer) constraintLiteral.getValue()).floatValue());
		else {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintClass.class).fatal(exception.getMessage());
			throw exception;
		}
	}

	@Override
	public AbstractConstraintValue calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		if (!this.isFinishedType() || !constraintLiteral.isFinishedNumberType())
			return new AbstractConstraintFormula(this, operator, constraintLiteral);
		else if (constraintLiteral.getValue() instanceof Double) {
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
			Logger.getLogger(AbstractConstraintLiteralFloat.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
