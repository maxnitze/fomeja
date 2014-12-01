package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.util.List;
import java.util.Map;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;

/**
 * Theorem describes a theorem by its constraints and variables.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Theorem {
	/** the abstract constraints of the theorem */
	private final List<AbstractConstraint> abstractConstraints;
	/** an assignment of variable names to their parameter objects */
	private final Map<String, ParameterObject> variablesMap;
	/** the size of the constraints list */
	private final int constraintsSize;

	/**
	 * Constructor for a new theorem.
	 * 
	 * @param constraints the new list of abstract constraints
	 * @param variables the new list of variable fields
	 * @param variablesMap the new assignment map
	 */
	public Theorem(List<AbstractConstraint> constraints, Map<String, ParameterObject> variablesMap) {
		this.abstractConstraints = constraints;
		this.variablesMap = variablesMap;

		this.constraintsSize = constraints.size();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public List<AbstractConstraint> getAbstractConstraint() {
		return this.abstractConstraints;
	}

	/**
	 * 
	 * @return
	 */
	public Map<String, ParameterObject> getVariablesMap() {
		return this.variablesMap;
	}

	/**
	 * 
	 * @return
	 */
	public int getConstraintSize() {
		return this.constraintsSize;
	}
}
