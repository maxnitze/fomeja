package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import de.agra.sat.koselleck.decompiling.datatypes.PrefixedField;

/**
 * 
 * @author Max Nitze
 */
public class ParameterObject {
	/**  */
	public final Object object;
	/**  */
	public final PrefixedField prefixedField;
	/**  */
	public final int index;
	
	/**
	 * 
	 * @param object
	 * @param prefixedField
	 * @param index
	 */
	public ParameterObject(Object object, PrefixedField prefixedField, int index) {
		this.object = object;
		this.prefixedField = prefixedField;
		this.index = index;
	}
	
	/**
	 * 
	 * @param object
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof ParameterObject))
			return false;
		
		ParameterObject parameterObject = (ParameterObject)object;
		return this.object.equals(parameterObject.object) && this.prefixedField.equals(parameterObject.prefixedField);
	}
}
