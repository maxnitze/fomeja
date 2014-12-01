package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.datatypes.PreField;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ComplexParameterObject extends ParameterObject {
	/** COMMENT */
	private final List<Collection<?>> objectRange;

	/**
	 * COMMENT
	 * 
	 * @param startingObject
	 * @param name
	 * @param preField
	 * @param index
	 * @param dependentParameterObject
	 * @parma objectRange
	 */
	public ComplexParameterObject(Object startingObject, String name, PreField preField, int index, ParameterObject dependentParameterObject, List<Collection<?>> objectRange) {
		super(startingObject, name, preField, index, dependentParameterObject);

		this.objectRange = objectRange;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<Collection<?>> getObjectRange() {
		return this.objectRange;
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
		Logger.getLogger(ComplexParameterObject.class).fatal(message);
		throw new IndexOutOfBoundsException(message);
	}
}
