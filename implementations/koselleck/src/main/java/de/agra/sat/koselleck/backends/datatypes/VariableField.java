package de.agra.sat.koselleck.backends.datatypes;

/**
 * VariableField describes a variable field by its name and type.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class VariableField {
	/** the name of the field */
	public final String variableName;
	/** the type of the field */
	public final Class<?> fieldType;

	/**
	 * Constructor for a new Variable Field.
	 * 
	 * @param variableName the name of the new variable field
	 * @param fieldType the type of the new variable field
	 */
	public VariableField(String variableName, Class<?> fieldType) {
		this.variableName = variableName;
		this.fieldType = fieldType;
	}

	/**
	 * equals compares this object with another given one. if the other is also
	 *  a variable field type the names are compared.
	 * 
	 * @param object the object to compare
	 * 
	 * @return {@code true} if the object is a variable field type and the
	 *  names are equal, {@code false} otherwise
	 */
	@Override
	public boolean equals(Object object) {
		if(!(object instanceof VariableField))
			return false;

		return this.variableName.equals(((VariableField) object).variableName);
	}
}
