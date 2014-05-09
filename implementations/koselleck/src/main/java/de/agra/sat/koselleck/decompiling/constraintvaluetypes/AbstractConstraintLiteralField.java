package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.lang.reflect.Field;
import java.util.Map;
import java.util.Set;

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

	/** constant table prefix of the field */
	public final String constantTablePrefix;
	/** the prefixed name of this field */
	public final String constantTablePrefixedName;

	/** the fields accessed before this field */
	public final Set<PreField> preFields;
	/** the prefixed name of this field with previous field names */
	public final String preFieldsPrefixedName;

	/** the replaced constraint value */
	private AbstractConstraintValue replacedConstraintValue;

	/**
	 * 
	 * @param value
	 * @param constantTablePrefix
	 * @param fieldCode
	 * @param fieldCodeIndex
	 * @param preFields
	 */
	public AbstractConstraintLiteralField(Field value, String constantTablePrefix, Opcode fieldCode, int fieldCodeIndex, Set<PreField> preFields) {
		super(value, (value != null && value.getAnnotation(Variable.class) != null), false, false);

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.constantTablePrefix = constantTablePrefix;
		this.constantTablePrefixedName = constantTablePrefix + value.getName();

		this.preFields = preFields;

		StringBuilder preFieldsPrefixedNameBuilder = new StringBuilder("v_");
		for(PreField preField : preFields)
			preFieldsPrefixedNameBuilder
					.append(preField.field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"));

		preFieldsPrefixedNameBuilder
				.append(value.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"))
				.append(value.getName());
		this.preFieldsPrefixedName = preFieldsPrefixedNameBuilder.toString();

		this.replacedConstraintValue = null;
	}

	@Override
	public void replaceAll(String regex, String replacement) {
		if (this.replacedConstraintValue == null && this.constantTablePrefixedName.matches(regex)) {
			if (replacement.matches("^\\d+(\\.\\d+)?d$"))
				this.replacedConstraintValue = new AbstractConstraintLiteralDouble(Double.parseDouble(replacement));
			else if (replacement.matches("^\\d+(\\.\\d+)?f$"))
				this.replacedConstraintValue = new AbstractConstraintLiteralFloat(Float.parseFloat(replacement));
			else if (replacement.matches("^\\d+$"))
				this.replacedConstraintValue = new AbstractConstraintLiteralInteger(Integer.parseInt(replacement));
			else
				this.replacedConstraintValue = new AbstractConstraintLiteralString(replacement);
		} else if (this.replacedConstraintValue != null)
			this.replacedConstraintValue.replaceAll(regex, replacement);
	}

	@Override
	public AbstractConstraintValue evaluate() {
		if (this.replacedConstraintValue != null)
			return this.replacedConstraintValue;
		else
			return this;
	}

	@Override
	public AbstractConstraintValue substitute(Map<Integer, Object> constraintArguments) {
		if (this.isVariable || constraintArguments.get(this.fieldCodeIndex) == null)
			return this;

		Object constraintArgument = constraintArguments.get(this.fieldCodeIndex);
		for (PreField preField : this.preFields) {
			preField.field.setAccessible(true);
			try {
				constraintArgument = preField.field.get(constraintArgument);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not access field \"" + preField.field + "\" on object \"" + constraintArgument + "\"";
				Logger.getLogger(AbstractConstraintLiteralField.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		}

		try {
			constraintArgument = this.value.get(constraintArgument);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + this.value + "\" on object \"" + constraintArgument + "\"";
			Logger.getLogger(AbstractConstraintLiteralField.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		if (constraintArgument instanceof Integer)
			return new AbstractConstraintLiteralInteger((Integer) constraintArgument);
		else if (constraintArgument instanceof Float)
			return new AbstractConstraintLiteralFloat((Float) constraintArgument);
		else if (constraintArgument instanceof Double)
			return new AbstractConstraintLiteralDouble((Double) constraintArgument);
		else
			return new AbstractConstraintLiteralObject(constraintArgument);
	}

	@Override
	public boolean matches(String regex) {
		if (this.replacedConstraintValue == null)
			return this.constantTablePrefixedName.matches(regex);
		else
			return this.replacedConstraintValue.matches(regex);
	}

	@Override
	public boolean equals(Object object) {
		if(!(object instanceof AbstractConstraintLiteralField))
			return false;

		AbstractConstraintLiteralField abstractConstraintLiteralField = (AbstractConstraintLiteralField) object;

		return this.value.equals(abstractConstraintLiteralField.value)
				&& this.constantTablePrefix.equals(abstractConstraintLiteralField.constantTablePrefix)
				&& this.isVariable == abstractConstraintLiteralField.isVariable;
	}

	@Override
	public AbstractConstraintLiteralField clone() {
		return new AbstractConstraintLiteralField(this.value, this.constantTablePrefix, this.fieldCode, this.fieldCodeIndex, this.preFields);
	}

	@Override
	public String toString() {
		if (this.replacedConstraintValue == null)
			return this.constantTablePrefixedName;
		else
			return this.replacedConstraintValue.toString();
	}

	@Override
	public int compareTo(AbstractConstraintLiteral<?> constraintLiteral) {
		NoComparableNumberTypeException exception = new NoComparableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}

	@Override
	public AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator) {
		NoCalculatableNumberTypeException exception = new NoCalculatableNumberTypeException(this);
		Logger.getLogger(AbstractConstraintLiteralField.class).fatal(exception.getMessage());
		throw exception;
	}
}
