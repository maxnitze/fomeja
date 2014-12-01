package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.ArrayList;

import de.agra.sat.koselleck.datatypes.PreField;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ParameterObjectList extends ArrayList<ParameterObject> {
	/** COMMENT */
	private static final long serialVersionUID = -2980968242073860387L;

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preField
	 * 
	 * @return
	 */
	public boolean contains(Object object, PreField preField) {
		for (ParameterObject parameterObject : this)
			if (parameterObject.getStartingObject().equals(object)
					&& parameterObject.getPreField().equals(preField))
				return true;

		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preField
	 * 
	 * @return
	 */
	public ParameterObject get(Object object, PreField preField) {
		for (ParameterObject parameterObject : this)
			if (parameterObject.getStartingObject().equals(object)
					&& parameterObject.getPreField().equals(preField))
				return parameterObject;

		return null;
	}

	/**
	 * COMMENT
	 * 
	 * @param preField
	 * 
	 * @return
	 */
	public int getMaxIndex(PreField preField) {
		int maxIndex = 0;
		for (ParameterObject parameterObject : this)
			if (parameterObject.getPreField().equals(preField))
				maxIndex = parameterObject.getIndex() > maxIndex ? parameterObject.getIndex() : maxIndex;

		return maxIndex;
	}
}
