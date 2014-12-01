package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import de.agra.sat.koselleck.datatypes.PreField;

/**
 * ParameterObject is an parameter object for a specific method (at index).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class ParameterObject {
	/** the object */
	private final Object startingObject;
	/** COMMENT */
	private String name;
	/** COMMENT */
	private final PreField preField;
	/** the index of the parameter */
	private final int index;
	/** COMMENT */
	private boolean isAssigned;
	/** COMMENT */
	private ParameterObject dependentParameterObject;

	/**
	 * COMMENT
	 * 
	 * @param startingObject
	 * @param name
	 * @param preField 
	 * @param index
	 * @param dependentParameterObject
	 */
	public ParameterObject(Object startingObject, String name, PreField preField, int index, ParameterObject dependentParameterObject) {
		this.startingObject = startingObject;
		this.name = name + "_" + index;
		this.preField = preField;
		this.index = index;
		this.isAssigned = false;
		this.dependentParameterObject = dependentParameterObject;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Object getStartingObject() {
		return this.startingObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreField getPreField() {
		return this.preField;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getIndex() {
		return this.index;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isAssigned() {
		return this.isAssigned;
	}

	/**
	 * COMMENT
	 */
	public void setAssigned() {
		this.isAssigned = true;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ParameterObject getDependentParameterObject() {
		return this.dependentParameterObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean hasDependentParameterObject() {
		return this.dependentParameterObject != null;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ParameterObject))
			return false;

		ParameterObject parameterObject = (ParameterObject) object;
		return this.startingObject.equals(parameterObject.startingObject)
				&& this.preField.equals(parameterObject.preField)
				&& this.index == parameterObject.index;
	}
}
