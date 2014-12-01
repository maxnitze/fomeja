package de.agra.sat.koselleck.datatypes;

/* imports */
import java.lang.reflect.Field;
import java.util.List;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PreField {
	/** COMMENT */
	private Field field;
	/** COMMENT */
	private boolean isVariable;

	/** COMMENT */
	private Opcode fieldCode;
	/** COMMENT */
	private int fieldCodeIndex;

	/** COMMENT */
	private int constantTableIndex;

	/** COMMENT */
	private PreFieldList preFieldList;

	/**
	 * COMMENT
	 * 
	 * @param field
	 * @param constantTablePrefix
	 * @param fieldCode
	 * @param fieldCodeIndex
	 * @param preFields
	 */
	public PreField(Field field, int constantTableIndex, Opcode fieldCode, int fieldCodeIndex, List<PreField> preFields) {
		this.field = field;
		this.isVariable = field != null && field.getAnnotation(Variable.class) != null;

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.constantTableIndex = constantTableIndex;

		this.preFieldList = new PreFieldList(fieldCodeIndex, fieldCode, preFields);
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Field getField() {
		return this.field;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Opcode getFieldCode() {
		return this.fieldCode;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getFieldCodeIndex() {
		return this.fieldCodeIndex;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getConstantTableIndex() {
		return this.constantTableIndex;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<PreField> getPreFieldList() {
		return this.preFieldList;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getSubName() {
		return this.constantTableIndex + "-" + this.field.getName();
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreField))
			return false;

		PreField preField = (PreField) object;

		return this.field.equals(preField.field)
				&& this.constantTableIndex == preField.constantTableIndex;
	}

	@Override
	public String toString() {
		return this.field.getName() + " (" + this.constantTableIndex + ")";
	}
}
