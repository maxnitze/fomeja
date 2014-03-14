package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.List;
import java.util.Map;

import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;

/**
 * Theorem describes a theorem by its constraints and variables.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Theorem {
	/** the abstract constraints of the theorem */
	public final List<AbstractConstraint> abstractConstraints;
	/** the variables of the theorem */
	public final List<VariableField> variables;
	/** an assignment of variable names to their parameter objects */
	public final Map<String, ParameterObject> variablesMap;
	/** the size of the constraints list */
	public final int constraintsSize;
	/** the size of the variables list */
	public final int variablesSize;
	
	/**
	 * Constructor for a new theorem.
	 * 
	 * @param constraints the new list of abstract constraints
	 * @param variables the new list of variable fields
	 * @param variablesMap the new assignment map
	 */
	public Theorem(List<AbstractConstraint> constraints, List<VariableField> variables, Map<String, ParameterObject> variablesMap) {
		this.abstractConstraints = constraints;
		this.variables = variables;
		this.variablesMap = variablesMap;
		
		this.constraintsSize = constraints.size();
		this.variablesSize = variables.size();
	}
}
