package de.agra.sat.koselleck.backends;

/** imports */
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintOperator;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;

/**
 * SMTII implements the smt2 pseudo boolean dialect.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class SMTII extends Dialect {
	/** pattern for a smt2 result constant (function without parameters) */
	private static final Pattern smt2ResultPattern = Pattern.compile("\\(define-fun (?<name>\\S+) \\(\\) (?<type>\\S+)(\n)?\\s*\\(?(?<value>(- \\d+|\\d+))\\)?");
	
	/**
	 * format formats the given single theorems by formatting its abstract
	 *  constraint representation.
	 * 
	 * @param singleTheorems the list of single theorems to format
	 * 
	 * @return the SMT II string representation of the given single theorems
	 *  based on the current component
	 * 
	 * @throws NotSatisfyableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	@Override
	public String format(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		return format(getConstraintForArguments(singleTheorems));
	}
	
	/**
	 * solveAndAssign 
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	@Override
	public void solveAndAssign(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		Theorem theorem = getConstraintForArguments(singleTheorems);
		
		String proverResult = this.prover.solve(format(theorem));
		
		Map<String, Object> resultMap = parseResult(proverResult);
		for(Map.Entry<String, ParameterObject> variable : theorem.variablesMap.entrySet()) {
			Object result = resultMap.get(variable.getKey());
			
			if(result != null) {
				variable.getValue().prefixedField.field.setAccessible(true);
				try {
					variable.getValue().prefixedField.field.set(variable.getValue().object, result);
				} catch (IllegalArgumentException | IllegalAccessException e) {
					String message = "could not access field \"" + variable.getValue().prefixedField.field.getName() +"\"";
					Logger.getLogger(SMTII.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			}
		}
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
		
		singleConstraintString.append(getOperatorOpening(singleConstraint.operator));
		singleConstraintString.append(" ");
		singleConstraintString.append(getBackendConstraintValue(singleConstraint.value1));
		singleConstraintString.append(" ");
		singleConstraintString.append(getBackendConstraintValue(singleConstraint.value2));
		singleConstraintString.append(getOperatorClosing(singleConstraint.operator));
		
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
		
		subConstraintString.append("(");
		subConstraintString.append(getConnectorName(subConstraint.connector));
		subConstraintString.append(" ");
		subConstraintString.append(getBackendConstraint(subConstraint.constraint1));
		subConstraintString.append(" ");
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
		constraintFormulaString.append(constraintFormula.operator.asciiName);
		constraintFormulaString.append(" ");
		constraintFormulaString.append(getBackendConstraintValue(constraintFormula.value1));
		constraintFormulaString.append(" ");
		constraintFormulaString.append(getBackendConstraintValue(constraintFormula.value2));
		constraintFormulaString.append(")");
		
		return constraintFormulaString.toString();
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * 
	 * @param theorem
	 * 
	 * @return
	 */
	private String format(Theorem theorem) {
		StringBuilder assignedConstraint = new StringBuilder();
		for(AbstractConstraint theoremConstraint : theorem.abstractConstraints) {
			String z3Constraint = getBackendConstraint(theoremConstraint);
			
			assignedConstraint.append("\n\t");
			assignedConstraint.append(z3Constraint);
		}
		
		StringBuilder smt2theorem = new StringBuilder();
		for(VariableField prefixedVariable : theorem.variables) {
			smt2theorem.append(getVariableDeclaration(prefixedVariable));
			smt2theorem.append("\n");
		}
		smt2theorem.append("(assert (and ");
		smt2theorem.append(assignedConstraint.toString());
		smt2theorem.append("\n))\n(check-sat)\n(get-model)");
		
		return smt2theorem.toString();
	}
	
	/**
	 * 
	 * @param connector
	 * 
	 * @return
	 */
	private String getConnectorName(BooleanConnector connector) {
		switch(connector) {
		case AND:
			return "and";
		case OR:
			return "or";
		default:
			Logger.getLogger(SMTII.class).fatal("boolean connector " + (connector == null ? "null" : "\"" + connector.code + "\"") + " is not known");
			throw new UnknownBooleanConnectorException(connector);
		}
	}
	
	/**
	 * 
	 * @param operator
	 * 
	 * @return
	 */
	private String getOperatorOpening(ConstraintOperator operator) {
		switch(operator) {
		case EQUAL:
			return "(=";
		case GREATER:
			return "(>";
		case GREATER_EQUAL:
			return "(not (<";
		case LESS:
			return "(<";
		case LESS_EQUAL:
			return "(not (>";
		case NOT_EQUAL:
			return "(not (=";
		default:
			Logger.getLogger(SMTII.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownConstraintOperatorException(operator);
		}
	}
	
	/**
	 * 
	 * @param operator
	 * 
	 * @return
	 */
	private String getOperatorClosing(ConstraintOperator operator) {
		switch(operator) {
		case EQUAL:
			return ")";
		case GREATER:
			return ")";
		case GREATER_EQUAL:
			return "))";
		case LESS:
			return ")";
		case LESS_EQUAL:
			return "))";
		case NOT_EQUAL:
			return "))";
		default:
			Logger.getLogger(SMTII.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
			throw new UnknownConstraintOperatorException(operator);
		}
	}
	
	/**
	 * 
	 * @param variableField
	 * 
	 * @return
	 */
	private String getVariableDeclaration(VariableField variableField) {
		StringBuilder variableDeclaration = new StringBuilder();
		variableDeclaration.append("(declare-const ");
		variableDeclaration.append(variableField.variableName);
		
		if(variableField.fieldType.equals(Integer.class))
			variableDeclaration.append(" Int)");
		else {
			String message = "could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.";
			Logger.getLogger(SMTII.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
		
		return variableDeclaration.toString();
	}
	
	/**
	 * 
	 * @param result
	 * 
	 * @return
	 */
	public Map<String, Object> parseResult(String result) {
		Map<String, Object> resultMap = new HashMap<String, Object>();
		
		Matcher resultMatcher = smt2ResultPattern.matcher(result);
		while(resultMatcher.find()) {
			if(resultMatcher.group("type").equals("Int"))
				resultMap.put(
						resultMatcher.group("name"),
						new Integer(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
			else {
				String message = "could not translate type \"" + resultMatcher.group("type") + "\" to Z3 syntax.";
				Logger.getLogger(SMTII.class).fatal(message);
				throw new IllegalArgumentException(message);
			}
		}
		
		return resultMap;
	}
}
