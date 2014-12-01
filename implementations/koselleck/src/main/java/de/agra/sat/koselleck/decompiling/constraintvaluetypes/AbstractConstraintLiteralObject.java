package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralObject extends AbstractConstraintLiteral<Object> {
	/**
	 * 
	 * @param value
	 */
	public AbstractConstraintLiteralObject(Object value) {
		super(value, false, true);
	}

	/**
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 */
	public AbstractConstraintLiteralObject(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, false, false);
	}

	/**
	 * 
	 * @param field
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param constantTableIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralObject(Field field, int fieldCodeIndex, Opcode opcode, int constantTableIndex, List<PreField> preFields) {
		super(field, fieldCodeIndex, opcode, constantTableIndex, false, false, preFields);
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void replaceAll(String regex, String replacement) {}

	@Override
	public AbstractConstraintValue evaluate() {
		return this;
	}

	@Override
	public AbstractConstraintLiteralObject clone() {
		if (this.isFinishedType())
			return new AbstractConstraintLiteralObject(this.getValue());
		else
			return new AbstractConstraintLiteralObject(this.getField(), this.getFieldCodeIndex(), this.getOpcode(), this.getConstantTableIndex(), this.getPreFieldList());
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
