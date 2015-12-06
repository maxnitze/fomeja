package de.agra.fomeja.backends.parameterobjects;

/* imports */
import de.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class RangedParameterObject extends ParameterObject {
	/**
	 * COMMENT
	 * 
	 * @param preFields
	 */
	public RangedParameterObject(PreFieldList preFields) {
		super(preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param dependentParameterObject
	 */
	public RangedParameterObject(PreFieldList preFields, ObjectParameterObject dependentParameterObject) {
		super(preFields, dependentParameterObject);
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
	public abstract Integer getObjectMapping(Object object);

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	protected Object getFieldObject(Object proverResult) {
		return this.getRangeElement((Integer) proverResult);
	}
}
