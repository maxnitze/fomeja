package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/* imports */
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
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralInteger extends AbstractConstraintLiteral<Integer> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralInteger(Integer value) {
		super(value, true, true);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 */
	public AbstractConstraintLiteralInteger(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, true, false);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @parma opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralInteger(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex, List<PreField> preFields) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, true, false, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 */
	public AbstractConstraintLiteralInteger(String name) {
		super(name, true, false);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintLiteralInteger))
			return false;

		AbstractConstraintLiteralInteger abstractConstraintLiteralInteger = (AbstractConstraintLiteralInteger)object;

		if (this.isFinishedType())
			return this.getValue().equals(abstractConstraintLiteralInteger.getValue());
		else
			return this.getField().equals(abstractConstraintLiteralInteger.getField())
					&& this.getName().equals(abstractConstraintLiteralInteger.getName())
					&& this.getFieldCodeIndex() == abstractConstraintLiteralInteger.getFieldCodeIndex()
					&& this.getOpcode().equals(abstractConstraintLiteralInteger.getOpcode())
					&& this.getConstantTableIndex() == abstractConstraintLiteralInteger.getConstantTableIndex();
	}

	@Override
	public AbstractConstraintLiteralInteger clone() {
		if (this.isFinishedType())
			return new AbstractConstraintLiteralInteger(this.getValue());
		else
			return new AbstractConstraintLiteralInteger(this.getField(), this.getFieldCodeIndex(), this.getOpcode(), this.getConstantTableIndex(), this.getPreFieldList());
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		if (!this.isFinishedType() || !constraintLiteral.isFinishedNumberType()) {
			NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
			Logger.getLogger(AbstractConstraintClass.class).fatal(exception.getMessage());
			throw exception;
		} else if (constraintLiteral.getValue() instanceof Double)
			return ((Double) this.getValue().doubleValue()).compareTo((Double) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Float)
			return ((Float) this.getValue().floatValue()).compareTo((Float) constraintLiteral.getValue());
		else if (constraintLiteral.getValue() instanceof Integer)
			return this.getValue().compareTo((Integer) constraintLiteral.getValue());
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
				return new AbstractConstraintLiteralFloat(this.getValue().floatValue() + ((Float) constraintLiteral.getValue()));
			case SUB:
				return new AbstractConstraintLiteralFloat(this.getValue().floatValue() - ((Float) constraintLiteral.getValue()));
			case MUL:
				return new AbstractConstraintLiteralFloat(this.getValue().floatValue() * ((Float) constraintLiteral.getValue()));
			case DIV:
				return new AbstractConstraintLiteralFloat(this.getValue().floatValue() / ((Float) constraintLiteral.getValue()));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else if (constraintLiteral.getValue() instanceof Integer) {
			switch(operator) {
			case ADD:
				return new AbstractConstraintLiteralInteger(this.getValue() + ((Integer) constraintLiteral.getValue()));
			case SUB:
				return new AbstractConstraintLiteralInteger(this.getValue() - ((Integer) constraintLiteral.getValue()));
			case MUL:
				return new AbstractConstraintLiteralInteger(this.getValue() * ((Integer) constraintLiteral.getValue()));
			case DIV:
				return new AbstractConstraintLiteralInteger(this.getValue() / ((Integer) constraintLiteral.getValue()));
			default:
				Logger.getLogger(AbstractConstraintFormula.class).fatal("arithmetic operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
				throw new UnknownArithmeticOperatorException(operator);
			}
		} else {
			NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(constraintLiteral);
			Logger.getLogger(AbstractConstraintLiteralInteger.class).fatal(exception.getMessage());
			throw exception;
		}
	}
}
