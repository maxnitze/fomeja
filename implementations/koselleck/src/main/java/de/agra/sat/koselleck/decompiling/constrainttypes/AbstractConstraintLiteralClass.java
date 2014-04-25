package de.agra.sat.koselleck.decompiling.constrainttypes;

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
	/** the opcode of the field */
	public final Opcode fieldCode;

	/**  */
	public final int fieldCodeIndex;

	/**
	 * 
	 * @param value
	 * @param fieldCode
	 * @param fieldCodeIndex
	 */
	public AbstractConstraintLiteralClass(Class<?> value, Opcode fieldCode, int fieldCodeIndex) {
		super(value, false, false, false);

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;
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
		if(!(object instanceof AbstractConstraintLiteralClass))
			return false;
		
		AbstractConstraintLiteralClass abstractConstraintLiteralObject = (AbstractConstraintLiteralClass)object;
		
		return this.value.equals(abstractConstraintLiteralObject.value) &&
				this.isVariable == abstractConstraintLiteralObject.isVariable;
	}

	@Override
	public AbstractConstraintLiteralClass clone() {
		return new AbstractConstraintLiteralClass(this.value, this.fieldCode, this.fieldCodeIndex);
	}

	@Override
	public String toString() {
		return this.value + "[" + (this.isVariable ? "variable;" : "not variable;") + " no number type]";
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
