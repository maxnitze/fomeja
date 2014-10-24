package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.agra.sat.koselleck.datatypes.PreField;

/**
 * 
 * @author Max Nitze
 */
public class ComplexParameterObject extends ParameterObject {
	/**  */
	private final List<Collection<?>> objectRange;

	/**
	 * 
	 * @param object
	 * @param preField
	 * @param index
	 */
	public ComplexParameterObject(Object object, PreField preField, int index, List<Collection<?>> objectRange) {
		super(object, preField, index);

		this.objectRange = objectRange;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public List<Collection<?>> getObjectRange() {
		return this.objectRange;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
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
			else {
				List<Object> objectRangeList = new ArrayList<Object>(objectRangeCollection);
				return objectRangeList.get(index);
			}
		}

		throw new IndexOutOfBoundsException("trying to access the element with index \"" + maxIndex + "\" but there are only \"" + (maxIndex - index) + "\" elements");
	}
}
