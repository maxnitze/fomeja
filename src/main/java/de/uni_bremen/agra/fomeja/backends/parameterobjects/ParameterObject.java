package de.uni_bremen.agra.fomeja.backends.parameterobjects;

/* imports */
import java.lang.reflect.Field;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.Dialect;
import de.uni_bremen.agra.fomeja.backends.datatypes.ResultModel;
import de.uni_bremen.agra.fomeja.datatypes.PreField;
import de.uni_bremen.agra.fomeja.datatypes.PreFieldList;

/**
 * COMMENT
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class ParameterObject {
	/** COMMENT */
	private PreFieldList preFieldList;
	/** COMMENT */
	private boolean isAssigned;
	/** COMMENT */
	private ObjectParameterObject dependentParameterObject;

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 */
	public ParameterObject(PreFieldList preFieldList) {
		this.preFieldList = preFieldList;

		this.isAssigned = false;
		this.dependentParameterObject = null;
	}

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * @param dependentParameterObject
	 */
	public ParameterObject(PreFieldList preFieldList, ObjectParameterObject dependentParameterObject) {
		this.preFieldList = preFieldList;

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
		return this.preFieldList.getObject();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return this.preFieldList.getName();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreFieldList getPreFieldList() {
		return this.preFieldList;
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
	public ObjectParameterObject getDependentParameterObject() {
		return this.dependentParameterObject;
	}

	/**
	 * COMMENT
	 * 
	 * @param dependentParameterObject
	 */
	public void setDependentParameterObject(ObjectParameterObject dependentParameterObject) {
		this.dependentParameterObject = dependentParameterObject;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isDependend() {
		return this.dependentParameterObject != null;
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param proverResult
	 * 
	 * @return
	 */
	protected abstract Object getFieldObject(Object proverResult);

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param proverResults
	 */
	public void assign(ResultModel resultModel) {
		Object proverResult = resultModel.getOrDefault(this.getName(), this.preFieldList.last().getField().getType());
		if (!this.isAssigned && proverResult != null) {
			if (this.isDependend() && !this.dependentParameterObject.isAssigned())
				this.dependentParameterObject.assign(resultModel);

			Object fieldObject = this.getFieldValue();

			Field field = this.preFieldList.last().getField();
			boolean accessibility = field.isAccessible(); 
			field.setAccessible(true);
			try {
				field.set(fieldObject, this.getFieldObject(proverResult));
			} catch (IllegalArgumentException | IllegalAccessException e) {
				String message = "could not access field \"" + field.getName() +"\" with value \"" + proverResult + "\": " + e.getMessage();
				Logger.getLogger(ParameterObject.class).fatal(message);
				throw new IllegalArgumentException(message); // TODO change Exception type
			} finally {
				field.setAccessible(accessibility);
			}

			this.setAssigned();
		}
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private Object getFieldValue() {
		Object object = this.preFieldList.getObject();
		for (PreField preField : this.preFieldList.head(-1))
			object = this.getFieldValue(object, preField.getField());

		return object;
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * @param field
	 * 
	 * @return
	 */
	private Object getFieldValue(Object object, Field field) {
		boolean accessibility = field.isAccessible();
		field.setAccessible(true);
		try {
			return field.get(object);
		} catch (IllegalArgumentException | IllegalAccessException e) {
			String message = "could not access field \"" + field.getName() + "\" on object \"" + object + "\"";
			Logger.getLogger(Dialect.class).fatal(message);
			throw new IllegalArgumentException(message + "\n" + e.getMessage()); // TODO change Exception type
		} finally {
			field.setAccessible(accessibility);
		}
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof ParameterObject))
			return false;

		ParameterObject parameterObject = (ParameterObject) object;
		return this.getObject().equals(parameterObject.getObject())
				&& this.preFieldList.equals(parameterObject.preFieldList);
	}

	@Override
	public String toString() {
		return this.getName();
	}
}
