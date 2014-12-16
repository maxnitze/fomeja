package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.agra.sat.koselleck.datatypes.PreField;
import de.agra.sat.koselleck.datatypes.PreFieldList;

/**
 * ParameterObject is an parameter object for a specific method (at index).
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class ParameterObject {
	/** the object */
	private final Object object;
	/** COMMENT */
	private String name;
	/** COMMENT */
	private final PreFieldList preFields;
	/** COMMENT */
	private boolean isAssigned;
	/** COMMENT */
	private RangedParameterObject dependentParameterObject;
	/** COMMENT */
	private Map<Object, Integer> objectMapping;
	/** COMMENT */
	private int maxObjectMapping;

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param name
	 * @param preFields
	 */
	public ParameterObject(Object object, PreFieldList preFields) {
		this.object = object;
		this.preFields = preFields;
		this.name = this.getName(object, preFields);

		this.isAssigned = false;
		this.dependentParameterObject = null;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * @param dependentParameterObject
	 */
	public ParameterObject(Object object, PreFieldList preFields, RangedParameterObject dependentParameterObject) {
		this.object = object;
		this.preFields = preFields;
		this.name = this.getName(object, preFields);

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
	public Object getObject() {
		return this.object;
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
	public PreFieldList getPreFieldList() {
		return this.preFields;
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
	public RangedParameterObject getDependentParameterObject() {
		return this.dependentParameterObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isDependend() {
		return this.dependentParameterObject != null;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param object
	 * 
	 * @return
	 */
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

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param preFields
	 * 
	 * @return
	 */
	private String getName(Object object, List<PreField> preFields) {
		StringBuilder name = new StringBuilder();
		name.append(object.getClass().getSimpleName());
		name.append("@");
		name.append(object.hashCode());

		for (PreField preField : preFields) {
			name.append("_");
			name.append(preField.getField().getName());
		}

		return name.toString();
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ParameterObject))
			return false;

		ParameterObject parameterObject = (ParameterObject) object;
		return this.object.equals(parameterObject.object)
				&& this.preFields.equals(parameterObject.preFields);
	}
}
