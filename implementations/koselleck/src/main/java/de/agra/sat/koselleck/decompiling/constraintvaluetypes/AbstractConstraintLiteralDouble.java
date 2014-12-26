package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
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
public class AbstractConstraintLiteralDouble extends AbstractConstraintLiteral<Double> {
	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralDouble(Double value) {
		super(value, true, true);
	}

	/**
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralDouble(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex) {
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
	public AbstractConstraintLiteralDouble(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex, List<PreField> preFields) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, true, false, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AbstractConstraintLiteralDouble(String name) {
		super(name, true, false);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {
		if (!this.isFinishedType() && this.getName().matches(regex)) {
			if (replacement.matches("^\\d+(\\.\\d+)?d$"))
				this.setValueAndFinish(Double.parseDouble(replacement));
			else if (replacement.matches("^\\d+(\\.\\d+)?f$"))
				this.setValueAndFinish(((Float) Float.parseFloat(replacement)).doubleValue());
			else if (replacement.matches("^\\d+$"))
				this.setValueAndFinish(((Integer) Integer.parseInt(replacement)).doubleValue());
			else 
				this.setName(replacement);
		}}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintLiteralDouble))
			return false;

		AbstractConstraintLiteralDouble abstractConstraintLiteralDouble = (AbstractConstraintLiteralDouble)object;

		if (this.isFinishedType())
			return this.getValue().equals(abstractConstraintLiteralDouble.getValue());
		else
			return this.getField().equals(abstractConstraintLiteralDouble.getField())
					&& this.getName().equals(abstractConstraintLiteralDouble.getName())
					&& this.getFieldCodeIndex() == abstractConstraintLiteralDouble.getFieldCodeIndex()
					&& this.getOpcode().equals(abstractConstraintLiteralDouble.getOpcode())
					&& this.getConstantTableIndex() == abstractConstraintLiteralDouble.getConstantTableIndex();
	}

	@Override
	public AbstractConstraintLiteralDouble clone() {
		if (this.isFinishedType())
			return new AbstractConstraintLiteralDouble(this.getValue());
		else
			return new AbstractConstraintLiteralDouble(this.getField(), this.getFieldCodeIndex(), this.getOpcode(), this.getConstantTableIndex(), this.getPreFieldList());
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (this.isFinishedType() || !constraintLiteral.isFinishedNumberType()) {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintClass.class).fatal(exception.getMessage());
			throw exception;
		} else if (constraintLiteral.getValue() instanceof Double)
			return this.getValue().compareTo((Double) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Float)
			return this.getValue().compareTo(((Float) constraintLiteral.getValue()).doubleValue());
		else if (constraintLiteral.getValue() instanceof Integer)
			return this.getValue().compareTo(((Integer) constraintLiteral.getValue()).doubleValue());
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
				return new AbstractConstraintLiteralDouble(this.getValue() + ((Double) constraintLiteral.getValue()));
			case SUB:
				return new AbstractConstraintLiteralDouble(this.getValue() - ((Double) constraintLiteral.getValue()));
			case MUL:
				return new AbstractConstraintLiteralDouble(this.getValue() * ((Double) constraintLiteral.getValue()));
			case DIV:
				return new AbstractConstraintLiteralDouble(this.getValue() / ((Double) constraintLiteral.getValue()));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.getValue() instanceof Float) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.getValue() + ((Float) constraintLiteral.getValue()).doubleValue());
			case SUB:
				return new AbstractConstraintLiteralDouble(this.getValue() - ((Float) constraintLiteral.getValue()).doubleValue());
			case MUL:
				return new AbstractConstraintLiteralDouble(this.getValue() * ((Float) constraintLiteral.getValue()).doubleValue());
			case DIV:
				return new AbstractConstraintLiteralDouble(this.getValue() / ((Float) constraintLiteral.getValue()).doubleValue());
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.getValue() instanceof Integer) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralDouble(this.getValue() + ((Integer) constraintLiteral.getValue()).doubleValue());
			case SUB:
				return new AbstractConstraintLiteralDouble(this.getValue() - ((Integer) constraintLiteral.getValue()).doubleValue());
			case MUL:
				return new AbstractConstraintLiteralDouble(this.getValue() * ((Integer) constraintLiteral.getValue()).doubleValue());
			case DIV:
				return new AbstractConstraintLiteralDouble(this.getValue() / ((Integer) constraintLiteral.getValue()).doubleValue());
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralDouble.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
