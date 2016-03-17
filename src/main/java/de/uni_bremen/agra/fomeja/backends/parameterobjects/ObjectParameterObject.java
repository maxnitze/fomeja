package de.uni_bremen.agra.fomeja.backends.parameterobjects;

/* imports */
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.datatypes.ComponentCollectionList;
import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ObjectParameterObject extends RangedParameterObject {
	/** COMMENT */
	private ComponentCollectionList objectRange;

	/** COMMENT */
	private Map<Object, Integer> objectMap;
	/** COMMENT */
	private int mappingIndex;

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param objectRange
	 */
	public ObjectParameterObject(PreFieldList preFields, ComponentCollectionList objectRange) {
		super(preFields);
		this.objectRange = objectRange;
		this.objectMap = new HashMap<Object, Integer>();
		this.mappingIndex = -1;
	}

	/**
	 * COMMENT
	 * 
	 * @param preFields
	 * @param objectRange
	 * @param dependentParameterObject
	 */
	public ObjectParameterObject(PreFieldList preFields, ComponentCollectionList objectRange, ObjectParameterObject dependentParameterObject) {
		super(preFields, dependentParameterObject);
		this.objectRange = objectRange;
		this.objectMap = new HashMap<Object, Integer>();
		this.mappingIndex = -1;
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
		if (index < 0) {
			String message = "trying to access a negative index \"" + index + "\" on parameter object";
			Logger.getLogger(ObjectParameterObject.class).fatal(message);
			throw new IndexOutOfBoundsException(message);
		}

		if (this.getPreFieldList().last().isVariable()) {
			int maxIndex = index;
			for (Collection<?> objectRangeCollection : this.objectRange) {
				if (index >= objectRangeCollection.size())
					index -= objectRangeCollection.size();
				else {
					int i=0;
					for (Object orcObject : objectRangeCollection)
						if (i++ == index)
							return orcObject;
				}
			}
	
			String message = "trying to access the element with index \"" + maxIndex + "\" but there are only \"" + this.objectRange.getComponentsSize() + "\" elements";
			Logger.getLogger(ObjectParameterObject.class).fatal(message);
			throw new IndexOutOfBoundsException(message);
		} else {
			for (Entry<Object, Integer> objectMapEntry : this.objectMap.entrySet())
				if (objectMapEntry.getValue().equals(index))
					return objectMapEntry.getKey();

			String message = "trying to access the element with index \"" + index + "\" but there are only \"" + (this.mappingIndex+1) + "\" elements";
			Logger.getLogger(ObjectParameterObject.class).fatal(message);
			throw new IndexOutOfBoundsException(message);
		}
	}

	@Override
	public Integer getObjectMapping(Object object) {
		if (this.getPreFieldList().last().isVariable()) {
			int index = 0;
			for (Collection<?> objectRangeCollection : this.objectRange) {
				for (Object orcObject : objectRangeCollection) {
					if (orcObject.equals(object))
						return index;
					else
						++index;
				}
			}

			String message = "could not find mapping for object \"" + object + "\"";
			Logger.getLogger(ObjectParameterObject.class).fatal(message);
			throw new IndexOutOfBoundsException(message);
		} else {
			if (this.objectMap.get(object) != null)
				return this.objectMap.get(object);
			else {
				this.objectMap.put(object, ++this.mappingIndex);
				return this.mappingIndex;
			}
		}
	}
}
