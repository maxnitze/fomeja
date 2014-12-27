package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ObjectParameterObject extends RangedParameterObject {
	/** COMMENT */
	private final ComponentCollectionList objectRange;

	/** COMMENT */
	private Map<Object, Integer> objectMapping;
	/** COMMENT */
	private int maxObjectMapping;

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param objectRange
	 */
	public ObjectParameterObject(Object object, PreFieldList preFields, ComponentCollectionList objectRange) {
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
	public ObjectParameterObject(Object object, PreFieldList preFields, ComponentCollectionList objectRange, ObjectParameterObject dependentParameterObject) {
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

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public int getRangeSize() {
		return this.objectRange.getComponentsSize();
	}

	@Override
	public Object getRangeElement(int index) {
		int maxIndex = index;
		for (Collection<?> objectRangeCollection : this.objectRange) {
			if (index >= objectRangeCollection.size())
				index -= objectRangeCollection.size();
			else
				return (new ArrayList<Object>(objectRangeCollection)).get(index);
		}

		String message = "trying to access the element with index \"" + maxIndex + "\" but there are only \"" + (maxIndex - index) + "\" elements";
		Logger.getLogger(ObjectParameterObject.class).fatal(message);
		throw new IndexOutOfBoundsException(message);
	}

	@Override
	public int getMapping(Object object) {
		if (this.objectMapping == null) {
			this.objectMapping = new HashMap<Object, Integer>();
			this.maxObjectMapping = -1;
		}

		Integer mapping = this.objectMapping.get(object);
		if (mapping == null) {
			this.objectMapping.put(object, ++this.maxObjectMapping);
			mapping = this.maxObjectMapping;
		}

		return mapping;
	}
}
