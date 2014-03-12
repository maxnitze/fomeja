package de.agra.sat.koselleck.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

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

	/** the opcode of the field */
	public final Opcode fieldCode;
	/**  */
	public final int fieldCodeIndex;

	/**  */
	public final List<PreField> preFields;
	/**  */
	public final String prefixedName;

	/**
	 * 
	 * @param field
	 * @param fieldCode
	 * @param fieldCodeIndex
	 */
	public PreField(Field field, Opcode fieldCode, int fieldCodeIndex, List<PreField> preFields) {
		this.field = field;
		this.isVariable = field != null && field.getAnnotation(Variable.class) != null;

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;

		this.preFields = preFields;

		StringBuilder prefixedNameBuilder = new StringBuilder("v_");
		for(PreField preField : preFields)
			prefixedNameBuilder.append(preField.field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1_"));
		prefixedNameBuilder.append(field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1"));
		prefixedNameBuilder.append("_");
		prefixedNameBuilder.append(field.getName());
		this.prefixedName = prefixedNameBuilder.toString();
	}

	@Override
	public boolean equals(Object object) {
		if(!(object instanceof PreField))
			return false;

		PreField preField = (PreField) object;
		
		return this.field.equals(preField.field)
				&& this.prefixedName.equals(preField.prefixedName);
	}
}
