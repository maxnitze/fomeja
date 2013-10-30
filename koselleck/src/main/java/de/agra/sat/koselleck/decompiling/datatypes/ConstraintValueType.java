package de.agra.sat.koselleck.decompiling.datatypes;

/**
 * An enumeration of the constraint value types.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ConstraintValueType {
	INTEGER("Integer", Integer.class),
	STRING("String", String.class),
	PREFIXED_FIELD("PrefixedField", PrefixedField.class);
	
	/** the name */
	public final String name;
	/** the class */
	public final Class<?> clazz;
	
	/**
	 * Constructor for a new constraint value type.
	 * 
	 * @param name the new name
	 * @param clazz the new class
	 */
	ConstraintValueType(String name, Class<?> clazz) {
		this.name = name;
		this.clazz = clazz;
	}
	
	/**
	 * fromClass returns the constraint value type with the given class.
	 * 
	 * @param clazz the class to look for
	 * 
	 * @return the constraint value type with the given class
	 */
	public static ConstraintValueType fromClass(Class<?> clazz) {
		for(ConstraintValueType vct : values())
			if(vct.clazz.equals(clazz))
				return vct;
		throw new IllegalArgumentException("no constant with class \"" + clazz.getName() + "\" found");
	}
}
