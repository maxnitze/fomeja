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
	Double("Double", Double.class, true, true),
	Float("Float", Float.class, true, true),
	Integer("Integer", Integer.class, true, true),
	
	STRING("String", String.class, false, true),
	PREFIXED_FIELD("PrefixedField", PrefixedField.class, false, true);
	
	/** the name */
	public final String name;
	/** the class */
	public final Class<?> clazz;
	
	/** flag that indicates that the type is finished */
	public final boolean isFinishedType;
	/** flag that indicates that the type is a comparable number type */
	public final boolean isComparableNumberType;
	
	/**
	 * Constructor for a new constraint value type.
	 * 
	 * @param name the new name
	 * @param clazz the new class
	 * @param isFinished the new finished flag
	 * @param isComparableNumberType the new comparable number type flag
	 */
	ConstraintValueType(String name, Class<?> clazz, boolean isFinished, boolean isComparableNumberType) {
		this.name = name;
		this.clazz = clazz;
		this.isFinishedType = isFinished;
		this.isComparableNumberType = isComparableNumberType;
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
	 * getComparableNumberTypeClasses returns the list of the classes of this
	 *  enumeration that are assignable from number.
	 * 
	 * @return the list of the classes of this enumeration that are assignable
	 *  from a comparable number type
	 */
	public static List<Class<?>> getComparableNumberTypeClasses() {
		List<Class<?>> numberTypeClasses = new ArrayList<Class<?>>();
		
		for(ConstraintValueType cvt : values())
			if(cvt.isComparableNumberType)
				numberTypeClasses.add(cvt.clazz);
		
		return numberTypeClasses;
	}
}
