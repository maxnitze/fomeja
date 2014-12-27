package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class RangedParameterObject extends ParameterObject {
	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 */
	public RangedParameterObject(Object object, PreFieldList preFields) {
		super(object, preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param dependentParameterObject
	 */
	public RangedParameterObject(Object object, PreFieldList preFields, ObjectParameterObject dependentParameterObject) {
		super(object, preFields, dependentParameterObject);
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public abstract int getRangeSize();

	/**
	 * COMMENT
	 * 
	 * @param index
	 * 
	 * @return
	 */
	public abstract Object getRangeElement(int index);

	/**
	 * COMMENT
	 * 
	 * @param object
	 * 
	 * @return
	 */
	public abstract int getMapping(Object object);
}
