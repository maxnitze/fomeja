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
	public final Field field;
	/**  */
	public final boolean isVariable;

	/**  */
	public final Opcode fieldCode;
	/**  */
	public final int fieldCodeIndex;

	/**  */
	public final String constantTablePrefix;
	/**  */
	public final String constantTablePrefixedName;

	/**  */
	public final Set<PreField> preFields;
	/**  */
	public final String preFieldsPrefixedName;

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
