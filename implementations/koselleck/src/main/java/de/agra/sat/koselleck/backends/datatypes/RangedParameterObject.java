package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.Collection;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class RangedParameterObject extends ParameterObject {
	/** COMMENT */
	private final ComponentCollectionList objectRange;

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param objectRange
	 */
	public RangedParameterObject(Object object, PreFieldList preFields, ComponentCollectionList objectRange) {
		super(object, preFields);

		this.objectRange = objectRange;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param objectRange
	 * @param dependentParameterObject
	 */
	public RangedParameterObject(Object object, PreFieldList preFields, ComponentCollectionList objectRange, RangedParameterObject dependentParameterObject) {
		super(object, preFields, dependentParameterObject);

		this.objectRange = objectRange;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ComponentCollectionList getObjectRange() {
		return this.objectRange;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getRangeSize() {
		return this.objectRange.getComponentsSize();
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param index
	 * 
	 * @return
	 */
	public Object getObjectRangeElement(int index) {
		int maxIndex = index;
		for (Collection<?> objectRangeCollection : this.objectRange) {
			if (index >= objectRangeCollection.size())
				index -= objectRangeCollection.size();
			else
				return (new ArrayList<Object>(objectRangeCollection)).get(index);
		}

		String message = "trying to access the element with index \"" + maxIndex + "\" but there are only \"" + (maxIndex - index) + "\" elements";
		Logger.getLogger(RangedParameterObject.class).fatal(message);
		throw new IndexOutOfBoundsException(message);
	}
}
