package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import de.agra.sat.koselleck.datatypes.PreField;

/**
 * ParameterObject is an parameter object for a specific method (at index).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class ParameterObject {
	/** the object */
	public final Object object;
	/** the prefixed field of the object */
	public final PreField preField;
	/** the index of the parameter */
	public final int index;

	/**
	 * Constructor for a new parameter object.
	 * 
	 * @param object the new object
	 * @param prefixedField the new prefixed field of the object
	 * @param index the index of the parameter
	 */
	public ParameterObject(Object object, PreField preField, int index) {
		this.object = object;
		this.preField = preField;
		this.index = index;
	}

	/**
	 * equals compares this object with another given one. if the other is also
	 *  a parameter object type the object and prefixed field are compared.
	 * 
	 * @param object the object to compare
	 * 
	 * @return {@code true} if the object is a parameter object type and the
	 *  objects and prefixed fields are equal, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ParameterObject))
			return false;

		ParameterObject parameterObject = (ParameterObject) object;
		return this.object.equals(parameterObject.object) && this.preField.equals(parameterObject.preField);
	}
}
