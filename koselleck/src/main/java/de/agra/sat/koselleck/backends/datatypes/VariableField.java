package de.agra.sat.koselleck.backends.datatypes;

/**
 * 
 * @author Max Nitze
 */
public class VariableField {
	/**  */
	public final String variableName;
	/**  */
	public final Class<?> fieldType;
	
	/**
	 * 
	 * @param variableName
	 * @param fieldType
	 */
	public VariableField(String variableName, Class<?> fieldType) {
		this.variableName = variableName;
		this.fieldType = fieldType;
	}
	
	/**
	 * 
	 * @param obj
	 * 
	 * @return
	 */
	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof VariableField))
			return false;
		
		return this.variableName.equals(((VariableField)obj).variableName);
	}
}
