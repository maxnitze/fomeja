package de.uni_bremen.agra.fomeja.datatypes;

/* imports */
import java.lang.reflect.Field;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.annotations.Variable;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PreField {
	/** COMMENT */
	private Field field;
	/** COMMENT */
	private boolean isVariable;

	/**
	 * COMMENT
	 * 
	 * @param field COMMENT
	 */
	public PreField(Field field) {
		this.field = field;
		this.isVariable = field != null && field.getAnnotation(Variable.class) != null;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Field getField() {
		return this.field;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreField))
			return false;

		PreField preField = (PreField) object;

		return this.field != null && preField.field != null && this.field.equals(preField.field)
				&& this.isVariable != preField.isVariable;
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(23, 67)
		.append(this.field)
		.append(this.isVariable)
		.toHashCode();
	}

	@Override
	public String toString() {
		return this.field != null ? this.field.getName() : "NULL";
	}
}
