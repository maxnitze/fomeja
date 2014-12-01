package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import de.agra.sat.koselleck.datatypes.PreField;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class SimpleParameterObject extends ParameterObject {
	/**
	 * COMMENT
	 * 
	 * @param startingObject
	 * @param name
	 * @param preField
	 * @param index
	 */
	public SimpleParameterObject(Object startingObject, String name, PreField preField, int index, ParameterObject dependentParameterObject) {
		super(startingObject, name, preField, index, dependentParameterObject);
	}
}
