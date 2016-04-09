package de.uni_bremen.agra.fomeja.backends.parameterobjects;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class RangedParameterObject extends ParameterObject {
	/**
	 * COMMENT
	 * 
	 * @param preFields COMMENT
	 */
	public RangedParameterObject(PreFieldList preFields) {
		super(preFields);
	}

	/**
	 * COMMENT
	 * 
	 * @param preFields COMMENT
	 * @param dependentParameterObject COMMENT
	 */
	public RangedParameterObject(PreFieldList preFields, ObjectParameterObject dependentParameterObject) {
		super(preFields, dependentParameterObject);
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract int getRangeSize();

	/**
	 * COMMENT
	 * 
	 * @param index COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Object getRangeElement(int index);

	/**
	 * COMMENT
	 * 
	 * @param object COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Integer getObjectMapping(Object object);

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	protected Object getFieldObject(Object proverResult) {
		return this.getRangeElement((Integer) proverResult);
	}
}
