package de.agra.sat.koselleck.decompiling.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * An enumeration of the constraint value types.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public enum ConstraintValueType {
	Double("Double", new ArrayList<Class<?>>(Arrays.asList(Double.class, double.class)), true, true),
	Float("Float", new ArrayList<Class<?>>(Arrays.asList(Float.class, float.class)), true, true),
	Integer("Integer", new ArrayList<Class<?>>(Arrays.asList(Integer.class, int.class)), true, true),
	
	String("String", new ArrayList<Class<?>>(Arrays.asList(String.class)), false, false),
	PrefixedField("PrefixedField", new ArrayList<Class<?>>(Arrays.asList(PrefixedField.class)), false, false),
	PrefixedClass("PrefixedClass", new ArrayList<Class<?>>(Arrays.asList(PrefixedClass.class)), false, false),
	
	Object("Object", new ArrayList<Class<?>>(), false, false),
	
	NULL("null", null, true, false);
	
	/** the name */
	public final String name;
	/** the class */
	public final List<Class<?>> classes;
	
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
	ConstraintValueType(String name, List<Class<?>> classes, boolean isFinished, boolean isComparableNumberType) {
		this.name = name;
		this.classes = classes;
		this.isFinishedType = isFinished;
		this.isComparableNumberType = isComparableNumberType;
	}
	
	/**
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public boolean hasClass(Class<?> clazz) {
		for(Class<?> cls : this.classes)
			if(cls.equals(clazz))
				return true;
		
		return false;
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
			for(Class<?> cls : cvt.classes)
				if(cls != null && cls.equals(clazz))
					return cvt;
		
		return Object;
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
				numberTypeClasses.addAll(cvt.classes);
		
		return numberTypeClasses;
	}
}
