package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.List;

/**
 * An enumeration of the constraint value types.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ConstraintValueType {
	DOUBLE("Double", Double.class, true),
	FLOAT("Float", Float.class, true),
	INTEGER("Integer", Integer.class, true),
	
	STRING("String", String.class, false),
	PREFIXED_FIELD("PrefixedField", PrefixedField.class, false);
	
	/** the name */
	public final String name;
	/** the class */
	public final Class<?> clazz;
	
	/** flag that indicates that the type is a number type */
	public final boolean isNumberType;
	
	/**
	 * Constructor for a new constraint value type.
	 * 
	 * @param name the new name
	 * @param clazz the new class
	 * @param isNumberType the new number type flag
	 */
	ConstraintValueType(String name, Class<?> clazz, boolean isNumberType) {
		this.name = name;
		this.clazz = clazz;
		this.isNumberType = isNumberType;
	}
	
	/**
	 * fromClass returns the constraint value type with the given class.
	 * 
	 * @param clazz the class to look for
	 * 
	 * @return the constraint value type with the given class
	 */
	public static ConstraintValueType fromClass(Class<?> clazz) {
		for(ConstraintValueType cvt : values())
			if(cvt.clazz.equals(clazz))
				return cvt;
		throw new IllegalArgumentException("no constant with class \"" + clazz.getName() + "\" found");
	}
	
	/**
	 * getNumberTypeClasses returns the list of the classes of this enumeration
	 *  that are assignable from number.
	 * 
	 * @return the list of the classes of this enumeration that are assignable
	 *  from number
	 */
	public static List<Class<?>> getNumberTypeClasses() {
		List<Class<?>> numberTypeClasses = new ArrayList<Class<?>>();
		
		for(ConstraintValueType cvt : values())
			if(cvt.isNumberType)
				numberTypeClasses.add(cvt.clazz);
		
		return numberTypeClasses;
	}
}
