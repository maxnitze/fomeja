package de.uni_bremen.agra.fomeja.backends.parameterobjects;

/* imports */
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class EnumParameterObject extends RangedParameterObject {
	/** COMMENT */
	private Class<Enum<?>> enumClass;

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param enumClass
	 */
	public EnumParameterObject(PreFieldList preFields, Class<Enum<?>> enumClass) {
		super(preFields);
		this.enumClass = enumClass;
	}

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param enumClass
	 * @param dependentParameterObject
	 */
	public EnumParameterObject(PreFieldList preFields, Class<Enum<?>> enumClass, ObjectParameterObject dependentParameterObject) {
		super(preFields, dependentParameterObject);
		this.enumClass = enumClass;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Class<Enum<?>> getEnumClass() {
		return this.enumClass;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public int getRangeSize() {
		return this.enumClass.getEnumConstants().length;
	}

	@Override
	public Object getRangeElement(int index) {
		if (index >= this.enumClass.getEnumConstants().length) {
			String message = "tried to access element \"" + index + "\" of enumeration \"" + this.enumClass.getSimpleName() + "\" with only \"" + this.enumClass.getEnumConstants().length + "\" elements";
			Logger.getLogger(EnumParameterObject.class).fatal(message);
			throw new IllegalArgumentException(message);
		} else
			return this.enumClass.getEnumConstants()[index];
	}

	@Override
	public Integer getObjectMapping(Object object) {
		if (object == null || !this.enumClass.equals(object.getClass())) {
			String message = "object \"" + object + "\" is no instance of enumeration \"" + this.enumClass.getSimpleName() + "\"";
			Logger.getLogger(EnumParameterObject.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		return this.enumClass.cast(object).ordinal();
	}
}
