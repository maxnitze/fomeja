package de.agra.sat.koselleck.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.Set;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class PreField {
	/**  */
	private Field field;
	/**  */
	private boolean isVariable;

	/**  */
	private Opcode fieldCode;
	/**  */
	private int fieldCodeIndex;

	/**  */
	private String constantTableIndex;

	/**
	 * 
	 * @param field
	 * @param constantTablePrefix
	 * @param fieldCode
	 * @param fieldCodeIndex
	 */
	public PreField(Field field, String constantTableIndex, Opcode fieldCode, int fieldCodeIndex, Set<PreField> preFields) {
		this.field = field;
		this.isVariable = field != null && field.getAnnotation(Variable.class) != null;

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.constantTableIndex = constantTableIndex;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

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
	public boolean isVariable() {
		return this.isVariable;
	}

	/**
	 * 
	 * @return
	 */
	public Opcode getFieldCode() {
		return this.fieldCode;
	}

	/**
	 * 
	 * @return
	 */
	public int getFieldCodeIndex() {
		return this.fieldCodeIndex;
	}

	/**
	 * 
	 * @return
	 */
	public String getConstantTableIndex() {
		return this.constantTableIndex;
	}

	/**
	 * 
	 * @return
	 */
	public String getSubName() {
		return "_" + this.constantTableIndex + "-" + this.field.getName();
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreField))
			return false;

		PreField preField = (PreField) object;

		return this.field.equals(preField.field)
				&& this.constantTableIndex.equals(preField.constantTableIndex);
	}

	@Override
	public String toString() {
		return this.field.getName() + " (" + this.constantTableIndex + ")";
	}
}
