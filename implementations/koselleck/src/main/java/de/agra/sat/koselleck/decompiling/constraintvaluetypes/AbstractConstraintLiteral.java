package de.agra.sat.koselleck.decompiling.constraintvaluetypes;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.types.ArithmeticOperator;

/**
 * AbstractConstraintLiteral represents a literal in a constraint value.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class AbstractConstraintLiteral<T> extends AbstractConstraintValue {
	/** the value of the literal */
	private final T value;

	/** the name of the value */
	private String name;

	/**  */
	private final Field field;
	/**  */
	private final List<PreField> preFields;
	/**  */
	private final int constantTableIndex;

	/** flag if the value is variable */
	private final boolean isVariable;

	/** flag that indicates if the value is a number type */
	private final boolean isNumberType;

	/** flag that indicates if the value is a finished type */
	private final boolean isFinishedType;

	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new value for the literal
	 * @param name the new name of the variable
	 * @param isVariable the new variable flag for the value
	 * @param isNumberType the new number type flag for the value
	 * @param isFinishedType the new finished type flag for the value
	 */
	public AbstractConstraintLiteral(T value, boolean isVariable, boolean isNumberType, boolean isFinishedType) {
		this.value = value;

		this.isVariable = isVariable;
		this.isNumberType = isNumberType;
		this.isFinishedType = isFinishedType;

		this.field = null;
		this.constantTableIndex = -1;
		this.preFields = new ArrayList<PreField>();
		this.name = "";
	}

	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new value for the literal
	 * @param field
	 * @param fieldCodeIndex
	 * @param constantTableIndex
	 * @param name the new name of the variable
	 * @param isVariable the new variable flag for the value
	 * @param isNumberType the new number type flag for the value
	 * @param isFinishedType the new finished type flag for the value
	 */
	public AbstractConstraintLiteral(T value, Field field, int fieldCodeIndex, int constantTableIndex, boolean isVariable, boolean isNumberType, boolean isFinishedType) {
		this.value = value;

		this.isVariable = isVariable;
		this.isNumberType = isNumberType;
		this.isFinishedType = isFinishedType;

		this.field = field;
		this.constantTableIndex = constantTableIndex;
		this.preFields = new ArrayList<PreField>();
		this.name = "v" + fieldCodeIndex + "_" + this.constantTableIndex + "-" + this.field.getName();
	}

	/**
	 * Constructor for a new AbstractConstraintLiteral.
	 * 
	 * @param value the new value for the literal
	 * @param field
	 * @param fieldCodeIndex
	 * @param constantTableIndex
	 * @param name the new name of the variable
	 * @param isVariable the new variable flag for the value
	 * @param isNumberType the new number type flag for the value
	 * @param isFinishedType the new finished type flag for the value
	 * @param preFields
	 */
	public AbstractConstraintLiteral(T value, Field field, int fieldCodeIndex, int constantTableIndex, boolean isVariable, boolean isNumberType, boolean isFinishedType, List<PreField> preFields) {
		this.value = value;

		this.isVariable = isVariable;
		this.isNumberType = isNumberType;
		this.isFinishedType = isFinishedType;

		this.field = field;
		this.preFields = new ArrayList<PreField>(preFields);

		this.name = "v" + fieldCodeIndex;
		this.constantTableIndex = constantTableIndex;
		for (PreField preField : this.preFields)
			this.name += preField.getSubName();
		this.name += "_" + this.constantTableIndex + "-" + this.field.getName();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public T getValue() {
		return this.value;
	}

	/**
	 * 
	 * @return
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * 
	 * @param name
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * 
	 * @return
	 */
	public Field getField() {
		return this.field;
	}

	/**
	 * 
	 * @return
	 */
	public List<PreField> getPreFields() {
		return this.preFields;
	}

	/**
	 * 
	 * @return
	 */
	public int getConstantTableIndex() {
		return this.constantTableIndex;
	}

	/**
	 * 
	 * @return
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/**
	 * 
	 * @return
	 */
	public boolean isNumberType() {
		return this.isNumberType;
	}

	/**
	 * 
	 * @return
	 */
	public boolean isFinishedType() {
		return this.isFinishedType;
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public abstract int compareTo(AbstractConstraintLiteral<?> constraintLiteral);

	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public abstract AbstractConstraintLiteral<?> calc(AbstractConstraintLiteral<?> constraintLiteral, ArithmeticOperator operator);
}
