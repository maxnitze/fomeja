package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class PrefixedField {
	/**  */
	public final Field field;
	/**  */
	public final Class<?> fieldType;
	/**  */
	public final Opcode fieldCode;
	/**  */
	public final int value;
	/**  */
	public final List<PrefixedField> preFields;
	/**  */
	public final String prefix;
	/**  */
	public final String prefixedName;
	/**  */
	public final String prefieldsPrefixedName;
	/**  */
	public final boolean isVariable;
	
	/**
	 * 
	 * @param field
	 * @param fieldType
	 * @param fieldCode
	 * @param value
	 * @param preFields
	 * @param prefix
	 */
	public PrefixedField(Field field, Class<?> fieldType, Opcode fieldCode, int value, List<PrefixedField> preFields, String prefix) {
		this.field = field;
		this.fieldType = fieldType;
		this.fieldCode = fieldCode;
		this.value = value;
		this.preFields = preFields;
		
		this.prefix = prefix;
		this.prefixedName = prefix + field.getName();
		
		StringBuilder prefieldsPrefixedNameBuilder = new StringBuilder("v_");
		for(PrefixedField preField : preFields) {
			prefieldsPrefixedNameBuilder.append(preField.field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1"));
			prefieldsPrefixedNameBuilder.append("_");
		}
		prefieldsPrefixedNameBuilder.append(field.getDeclaringClass().getName().replaceAll(".*\\.([^\\.]+)$", "$1"));
		prefieldsPrefixedNameBuilder.append("_");
		prefieldsPrefixedNameBuilder.append(field.getName());
		this.prefieldsPrefixedName = prefieldsPrefixedNameBuilder.toString();
		
		if(this.field.getAnnotation(Variable.class) != null)
			this.isVariable = true;
		else
			this.isVariable = false;
	}
}
