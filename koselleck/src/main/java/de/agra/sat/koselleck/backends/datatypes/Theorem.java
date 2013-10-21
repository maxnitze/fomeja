package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.List;
import java.util.Map;

import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;

/**
 * 
 * @author Max Nitze
 */
public class Theorem {
	/**  */
	public final List<String> stringConstraints;
	/**  */
	public final List<AbstractConstraint> abstractConstraints;
	/**  */
	public final List<VariableField> variables;
	/**  */
	public final Map<String, ParameterObject> variablesMap;
	/**  */
	public final int constraintsSize;
	/**  */
	public final int variablesSize;
	
	/**
	 * 
	 * @param constraints
	 * @param variables
	 * @param variablesMap
	 */
	public Theorem(List<String> constraints, List<VariableField> variables, Map<String, ParameterObject> variablesMap) {
		this.stringConstraints = constraints;
		this.abstractConstraints = null;
		this.variables = variables;
		this.variablesMap = variablesMap;
		
		this.constraintsSize = constraints.size();
		this.variablesSize = variables.size();
	}
	
	/**
	 * 
	 * @param variablesMap
	 * @param constraints
	 * @param variables
	 */
	public Theorem(Map<String, ParameterObject> variablesMap, List<AbstractConstraint> constraints, List<VariableField> variables) {
		this.stringConstraints = null;
		this.abstractConstraints = constraints;
		this.variables = variables;
		this.variablesMap = variablesMap;
		
		this.constraintsSize = constraints.size();
		this.variablesSize = variables.size();
	}
}
