package de.agra.sat.koselleck.backends;

/** imports */
import java.io.IOException;
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
import de.agra.sat.koselleck.utils.IOUtils;

/**
 * 
 * @author Max Nitze
 */
public class Z3 extends TheoremProver {
	/**  */
	Pattern z3resultPattern = Pattern.compile("\\(define-fun (?<name>\\S+) \\(\\) (?<type>\\S+)(\n)?\\s*\\(?(?<value>(- \\d+|\\d+))\\)?");
	
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
		return format(getConstraintForArguments(singleTheorems));
	}
	
	/**
	 * 
	 * @param singleTheorems
	 * 
	 * @return
	 * 
	 * @throws NotSatisfyableException
	 */
	@Override
	public void solveAndAssign(List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		Theorem theorem = getConstraintForArguments(singleTheorems);
		
		String z3theorem = format(theorem);
		
		IOUtils.writeToFile("/home/max/Documents/code.txt", z3theorem);
		
		Process p = null;
		try {
			p = Runtime.getRuntime().exec("/home/max/Downloads/z3/bin/z3 -smt2 -file:/home/max/Documents/code.txt");
		} catch (IOException e) {
			String message = "could not execute z3 with the given file";
			Logger.getLogger(Z3.class).fatal(message);
			throw new IllegalArgumentException(message); // TODO other exception type
		}
		String proverResult = IOUtils.readFromStream(p.getInputStream());
		
		Map<String, Object> resultMap = parseResult(proverResult);
		for(Map.Entry<String, ParameterObject> variable : theorem.variablesMap.entrySet()) {
			Object result = resultMap.get(variable.getKey());
			
			if(result != null) {
				variable.getValue().prefixedField.field.setAccessible(true);
				try {
					variable.getValue().prefixedField.field.set(variable.getValue().object, result);
				} catch (IllegalArgumentException | IllegalAccessException e) {
					String message = "could not access field \"" + variable.getValue().prefixedField.field.getName() +"\"";
					Logger.getLogger(Z3.class).fatal(message);
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
		
		StringBuilder z3theorem = new StringBuilder();
		for(VariableField prefixedVariable : theorem.variables) {
			z3theorem.append(getVariableDeclaration(prefixedVariable));
			z3theorem.append("\n");
		}
		z3theorem.append("(assert (and ");
		z3theorem.append(assignedConstraint.toString());
		z3theorem.append("\n))\n(check-sat)\n(get-model)");
		
		return z3theorem.toString();
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
			Logger.getLogger(Z3.class).fatal("boolean connector " + (connector == null ? "null" : "\"" + connector.code + "\"") + " is not known");
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
			Logger.getLogger(Z3.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
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
			Logger.getLogger(Z3.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.asciiName + "\"") + " is not known");
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
			Logger.getLogger(Z3.class).fatal("could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.");
			throw new IllegalArgumentException("could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.");
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
		
		Matcher resultMatcher = z3resultPattern.matcher(result);
		while(resultMatcher.find()) {
			if(resultMatcher.group("type").equals("Int"))
				resultMap.put(
						resultMatcher.group("name"),
						new Integer(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
			else {
				Logger.getLogger(Z3.class).fatal("could not translate type \"" + resultMatcher.group("type") + "\" to Z3 syntax.");
				throw new IllegalArgumentException("could not translate type \"" + resultMatcher.group("type") + "\" to Z3 syntax.");
			}
		}
		
		return resultMap;
	}
}
