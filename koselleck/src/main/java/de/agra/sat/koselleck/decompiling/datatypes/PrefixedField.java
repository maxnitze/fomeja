package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.List;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.disassembling.datatypes.Opcode;

/**
 * PrefixedField describes a field disassembled by java disassembler (javac).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class PrefixedField {
	/** the field */
	public final Field field;
	/** the type of the field */
	public final Class<?> fieldType;
	/** the opcode of the field */
	public final Opcode fieldCode;
	/** the value */
	public final int value;
	/** the fields accessed before this field */
	public final List<PrefixedField> preFields;
	/** the prefix of the name of this field */
	public final String prefix;
	/** the prefixed name of this field */
	public final String prefixedName;
	/** the prefields prefixed name of this field */
	public final String prefieldsPrefixedName;
	/** a flag that indicates if this field is variable */
	public final boolean isVariable;
	
	/**
	 * Constructor for a new prefixed field.
	 * 
	 * @param field the new field
	 * @param fieldType the new type of the field
	 * @param fieldCode the new opcode of the field
	 * @param value the new value
	 * @param preFields the new list of prefields
	 * @param prefix the new prefix of the name of this field
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
