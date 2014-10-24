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
	private String constantTablePrefix;
	/**  */
	private String constantTablePrefixedName;

	/**  */
	private Set<PreField> preFields;
	/**  */
	private String preFieldsPrefixedName;

	/**
	 * 
	 * @param field
	 * @param constantTablePrefix
	 * @param fieldCode
	 * @param fieldCodeIndex
	 */
	public PreField(Field field, String constantTablePrefix, Opcode fieldCode, int fieldCodeIndex, Set<PreField> preFields) {
		this.field = field;
		this.isVariable = field != null && field.getAnnotation(Variable.class) != null;

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.constantTablePrefix = constantTablePrefix;
		this.constantTablePrefixedName = constantTablePrefix + field.getName();

		this.preFields = preFields;

		StringBuilder preFieldsPrefixedNameBuilder = new StringBuilder("v_");
		for (PreField preField : preFields)
			preFieldsPrefixedNameBuilder
					.append(preField.field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"));

		preFieldsPrefixedNameBuilder
			.append(field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"))
			.append(field.getName());
		this.preFieldsPrefixedName = preFieldsPrefixedNameBuilder.toString();
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
	public String getConstantTablePrefix() {
		return this.constantTablePrefix;
	}

	/**
	 * 
	 * @return
	 */
	public String getConstantTablePrefixedName() {
		return this.constantTablePrefixedName;
	}

	/**
	 * 
	 * @return
	 */
	public Set<PreField> getPreFields() {
		return this.preFields;
	}

	/**
	 * 
	 * @return
	 */
	public String getPreFieldsPrefixedName() {
		return this.preFieldsPrefixedName;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreField))
			return false;

		PreField preField = (PreField) object;

		return this.field.equals(preField.field)
				&& this.constantTablePrefixedName.equals(preField.constantTablePrefixedName);
	}

	@Override
	public String toString() {
		return this.constantTablePrefixedName + " (" + this.preFieldsPrefixedName + ")";
	}
}
