package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralClass extends AbstractConstraintLiteral<Class<?>> {

	/**
	 * COMMENT
	 * 
	 * @param value
	 * @param opcode
	 * @param fieldCodeIndex
	 */
	public AbstractConstraintLiteralClass(Class<?> value, Opcode opcode, int fieldCodeIndex) {
		super(value, fieldCodeIndex, opcode, false, false);
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
	public boolean equals(Object object) {
		if (!(object instanceof AbstractConstraintLiteralClass))
			return false;

		AbstractConstraintLiteralClass abstractConstraintLiteralObject = (AbstractConstraintLiteralClass) object;

		if (this.isFinishedType())
			return this.getValue().equals(abstractConstraintLiteralObject.getValue());
		else
			return this.getField().equals(abstractConstraintLiteralObject.getField())
					&& this.getName().equals(abstractConstraintLiteralObject.getName())
					&& this.getFieldCodeIndex() == abstractConstraintLiteralObject.getFieldCodeIndex()
					&& this.getOpcode().equals(abstractConstraintLiteralObject.getOpcode())
					&& this.getConstantTableIndex() == abstractConstraintLiteralObject.getConstantTableIndex();
	}

	@Override
	public AbstractConstraintLiteralClass clone() {
		return new AbstractConstraintLiteralClass(this.getValue(), this.getOpcode(), this.getFieldCodeIndex());
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralClass.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralClass.class).fatal(exception.getMessage());
		throw exception;
	}
}
