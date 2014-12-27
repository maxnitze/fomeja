package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreFieldList;

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
	 * @param object
	 * @param preFields
	 * @param enumClass
	 */
	public EnumParameterObject(Object object, PreFieldList preFields, Class<Enum<?>> enumClass) {
		super(object, preFields);

		this.enumClass = enumClass;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param enumClass
	 * @param dependentParameterObject
	 */
	public EnumParameterObject(Object object, PreFieldList preFields, Class<Enum<?>> enumClass, ObjectParameterObject dependentParameterObject) {
		super(object, preFields, dependentParameterObject);

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
		return this.enumClass.getEnumConstants()[index];
	}

	@Override
	public int getMapping(Object object) {
		if (this.enumClass.isInstance(object)) {
			return ((Enum<?>) object).ordinal();
		} else {
			String message = "\"" + object + "\" is not element of enum class \"" + this.enumClass.getSimpleName() + "\"";
			Logger.getLogger(EnumParameterObject.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}
}
