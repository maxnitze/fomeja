package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/* imports */
import java.lang.reflect.Field;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;

import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralEnum extends AbstractConstraintLiteral<Enum<?>> {
	/**
	 * COMMENT
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralEnum(Enum<?> value) {
		super(value, false, true);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 */
	public AbstractConstraintLiteralEnum(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, false, false);
	}

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralEnum(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex, List<PreField> preFields) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, false, false, preFields);
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public AbstractConstraintValue clone() {
		if (this.isFinishedType())
			return new AbstractConstraintLiteralEnum(this.getValue());
		else
			return new AbstractConstraintLiteralEnum(this.getField(), this.getFieldCodeIndex(), this.getOpcode(), this.getConstantTableIndex(), this.getPreFieldList());
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralObject.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralObject.class).fatal(exception.getMessage());
		throw exception;
	}
}
