package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */

/**
 * 
 * @author Max Nitze
 */
public enum ConstraintValueType {
	INTEGER("Integer", Integer.class),
	STRING("String", String.class),
	PREFIXED_FIELD("PrefixedField", PrefixedField.class),
	
	NULL("", null);
	
	/**  */
	public final String name;
	/**  */
	public final Class<?> clazz;
	
	/**
	 * 
	 * @param name
	 * @param clazz
	 */
	ConstraintValueType(String name, Class<?> clazz) {
		this.name = name;
		this.clazz = clazz;
	}
	
	/**
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static ConstraintValueType fromClass(Class<?> clazz) {
		for(ConstraintValueType vct : values())
			if(vct.clazz.equals(clazz))
				return vct;
		throw new IllegalArgumentException("no constant with class \"" + clazz.getName() + "\" found");
	}
}
