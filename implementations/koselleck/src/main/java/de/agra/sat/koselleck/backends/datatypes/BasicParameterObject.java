package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class BasicParameterObject extends ParameterObject {
	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 */
	public BasicParameterObject(Object object, PreFieldList preFields) {
		super(object, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param dependentParameterObject
	 */
	public BasicParameterObject(Object object, PreFieldList preFields, ObjectParameterObject dependentParameterObject) {
		super(object, preFields, dependentParameterObject);
	}
}
