package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.LinkedList;

import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ParameterObjectList extends LinkedList<ParameterObject> {
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
	public boolean contains(Object object, PreFieldList preFieldList) {
		for (ParameterObject parameterObject : this)
			if (parameterObject.getObject() == object
					&& parameterObject.getPreFieldList().equals(preFieldList))
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
	public ParameterObject get(Object object, PreFieldList preFieldList) {
		for (ParameterObject parameterObject : this)
			if (parameterObject.getObject() == object
					&& parameterObject.getPreFieldList().equals(preFieldList))
				return parameterObject;

		return null;
	}
}
