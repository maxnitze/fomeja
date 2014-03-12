package de.agra.sat.koselleck.decompiling.constrainttypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.exceptions.NoCalculatableNumberTypeException;
import de.agra.sat.koselleck.exceptions.NoComparableNumberTypeException;
import de.agra.sat.koselleck.types.ArithmeticOperator;
import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class AbstractConstraintLiteralField extends AbstractConstraintLiteral<Field> {
	/** the opcode of the field */
	public final Opcode fieldCode;

	/** the index of the field code */
	public final int fieldCodeIndex;

	/** the fields accessed before this field */
	public final List<PreField> preFields;
	/** the prefixed name of this field */
	public final String prefixedName;

	/**
	 * 
	 * @param value
	 * @param fieldCode
	 * @param fieldCodeIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralField(Field value, Opcode fieldCode, int fieldCodeIndex, List<PreField> preFields) {
		super(value, (value != null && value.getAnnotation(Variable.class) != null), false, false);

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.preFields = preFields;

		StringBuilder prefixedNameBuilder = new StringBuilder("v_");
		for(PreField preField : preFields)
			prefixedNameBuilder.append(preField.field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"));
		prefixedNameBuilder.append(value.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1"));
		prefixedNameBuilder.append("_");
		prefixedNameBuilder.append(value.getName());
		this.prefixedName = prefixedNameBuilder.toString();
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
		if(!(object instanceof AbstractConstraintLiteralField))
			return false;
		
		AbstractConstraintLiteralField abstractConstraintLiteralField = (AbstractConstraintLiteralField)object;
		
		return this.value.equals(abstractConstraintLiteralField.value) &&
				this.isVariable == abstractConstraintLiteralField.isVariable;
	}

	@Override
	public AbstractConstraintLiteral<Field> clone() {
		return new AbstractConstraintLiteralField(this.value, this.fieldCode, this.fieldCodeIndex, this.preFields);
	}

	@Override
	public String toString() {
		return this.value + "[" + (this.isVariable ? " variable;" : " not variable;") + " no number type]";
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> add(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> sub(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> mul(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> div(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}
}
