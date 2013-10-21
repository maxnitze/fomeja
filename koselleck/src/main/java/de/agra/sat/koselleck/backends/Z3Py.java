package de.agra.sat.koselleck.backends;

/** imports */
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;

/**
 * 
 * @author Max Nitze
 */
public class Z3Py extends TheoremProver {
	/**
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	@Override
	public String format(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		Theorem theorem = getConstraintForArguments(singleTheorems);
		
		StringBuilder assignedConstraint = new StringBuilder();
		for(AbstractConstraint theoremConstraint : theorem.abstractConstraints) {
			String z3Constraint = getBackendConstraint(theoremConstraint);
			
			if(assignedConstraint.length() > 0)
				assignedConstraint.append(", ");
			assignedConstraint.append(z3Constraint);
		}
		
		StringBuilder z3pytheorem = new StringBuilder();
		for(VariableField prefixedVariable : theorem.variables) {
			z3pytheorem.append(getVariableDeclaration(prefixedVariable));
			z3pytheorem.append("\n");
		}
		z3pytheorem.append("solve(");
		z3pytheorem.append(assignedConstraint.toString());
		z3pytheorem.append(")");
		
		return z3pytheorem.toString();
	}
	
	/**
	 * 
	 * @param constraint
	 * @param clazz
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	@Override
	public void solveAndAssign(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		// TODO implement
	}
	
	/**
	 * 
	 * @param booleanConstraint
	 * 
	 * @return
	 */
	@Override
	public String prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint) {
		return booleanConstraint.value ? "True" : "False";
	}
	
	/**
	 * 
	 * @param singleConstraint
	 * 
	 * @return
	 */
	@Override
	public String prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint) {
		StringBuilder singleConstraintString = new StringBuilder();
		
		singleConstraintString.append(getBackendConstraintValue(singleConstraint.value1));
		singleConstraintString.append(singleConstraint.operator.asciiName);
		singleConstraintString.append(getBackendConstraintValue(singleConstraint.value2));
		
		return singleConstraintString.toString();
	}
	
	/**
	 * 
	 * @param subConstraint
	 * 
	 * @return
	 */
	@Override
	public String prepareAbstractSubConstraint(AbstractSubConstraint subConstraint) {
		StringBuilder subConstraintString = new StringBuilder();
		
		subConstraintString.append(getConnectorName(subConstraint.connector));
		subConstraintString.append("(");
		subConstraintString.append(getBackendConstraint(subConstraint.constraint1));
		subConstraintString.append(", ");
		subConstraintString.append(getBackendConstraint(subConstraint.constraint2));
		subConstraintString.append(")");
		
		return subConstraintString.toString();
	}
	
	/**
	 * 
	 * @param constraintLiteral
	 * 
	 * @return
	 */
	public String prepareAbstractConstraintLiteral(AbstractConstraintLiteral constraintLiteral) {
		return constraintLiteral.value.toString();
	}
	
	/**
	 * 
	 * @param constraintFormula
	 * 
	 * @return
	 */
	public String prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula) {
		StringBuilder constraintFormulaString = new StringBuilder();
		
		constraintFormulaString.append("(");
		constraintFormulaString.append(getBackendConstraintValue(constraintFormula.value1));
		constraintFormulaString.append(constraintFormula.operator.asciiName);
		constraintFormulaString.append(getBackendConstraintValue(constraintFormula.value2));
		constraintFormulaString.append(")");
		
		return constraintFormulaString.toString();
	}
	
	/** private static methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param connector
	 * 
	 * @return
	 */
	private static String getConnectorName(BooleanConnector connector) {
		switch(connector) {
		case AND:
			return "And";
		case OR:
			return "Or";
		default:
			Logger.getLogger(Z3Py.class).fatal("boolean connector " + (connector == null ? "null" : "\"" + connector.code + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(connector);
		}
	}
	
	/**
	 * 
	 * @param variableField
	 * 
	 * @return
	 */
	private static String getVariableDeclaration(VariableField variableField) {
		StringBuilder variableDeclaration = new StringBuilder(variableField.variableName);
		
		if(variableField.fieldType.equals(Integer.class)) {
			variableDeclaration.append(" = Int('");
			variableDeclaration.append(variableField.variableName);
			variableDeclaration.append("')");
		} else {
			Logger.getLogger(Z3Py.class).fatal("could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.");
			throw new IllegalArgumentException("could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.");
		}
		
		return variableDeclaration.toString();
	}
}
