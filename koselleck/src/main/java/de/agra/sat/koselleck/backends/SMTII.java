package de.agra.sat.koselleck.backends;

/** imports */
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractPrematureConstraintValue;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.datatypes.BooleanConnector;
import de.agra.sat.koselleck.decompiling.datatypes.ConstraintOperator;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.exceptions.UnsupportedVariableTypeException;

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
	 * Constructor for a new SMTII dialect.
	 */
	public SMTII() {
		super(Dialect.Type.smt2);
	}
	
	/**
	 * format returns the smt2 string representation of the given theorem.
	 * 
	 * @param theorem the theorem to get the smt2 string representation for
	 * 
	 * @return the smt2 string representation for the given theorem
	 */
	@Override
	public String format(Theorem theorem) {
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
	 * parseResult parses the result from the theorem prover and returns an map
	 *  representing the result configuration.
	 * 
	 * @param result the result to parse
	 * 
	 * @return a map representing the result configuration
	 */
	@Override
	public Map<String, Object> parseResult(String result) {
		Map<String, Object> resultMap = new HashMap<String, Object>();
		
		Matcher resultMatcher = smt2ResultPattern.matcher(result);
		while(resultMatcher.find()) {
			if(resultMatcher.group("type").equals("Int"))
				resultMap.put(
						resultMatcher.group("name"),
						new Integer(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
			else if(resultMatcher.group("type").equals("Real"))
				resultMap.put(
						resultMatcher.group("name"),
						new Float(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
			else {
				Logger.getLogger(SMTII.class).fatal("could not translate type \"" + resultMatcher.group("type") + "\" to Z3 syntax.");
				throw new UnsupportedVariableTypeException(resultMatcher.group("type"));
			}
		}
		
		return resultMap;
	}
	
	/** ----- ----- ----- ----- ----- */
	
	/**
	 * prepareAbstractBooleanConstraint returns the smt2 string representation
	 *  of an abstract boolean constraint.
	 * 
	 * @param booleanConstraint the abstract boolean constraint to get the smt2
	 *  string representation from
	 * 
	 * @return the smt2 string representation for the given abstract boolean
	 *  constraint
	 */
	@Override
	public String prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint) {
		return booleanConstraint.value ? "True" : "False";
	}
	
	/**
	 * prepareAbstractSingleConstraint returns the smt2 string representation
	 *  of an abstract single constraint.
	 * 
	 * @param singleConstraint the abstract single constraint to get the smt2
	 *  string representation for
	 * 
	 * @return the smt2 string representation for the given abstract single
	 *  constraint
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
	 * prepareAbstractSubConstraint returns the smt2 string representation of
	 *  an abstract sub-constraint.
	 * 
	 * @param subConstraint the abstract sub-constraint to get the smt2 string
	 *  representation for
	 * 
	 * @return the smt2 string representation for the given abstract sub-
	 *  constraint
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
	 * prepareAbstractConstraintLiteral returns the smt2 string representation
	 *  of an abstract constraint literal.
	 * 
	 * @param singleConstraint the abstract constraint literal to get the smt2
	 *  string representation for
	 * 
	 * @return the smt2 string representation for the given abstract constraint
	 *  literal
	 */
	public String prepareAbstractConstraintLiteral(AbstractConstraintLiteral constraintLiteral) {
		return constraintLiteral.value.toString();
	}
	
	/**
	 * prepareAbstractConstraintFormula returns the smt2 string representation
	 *  of an abstract constraint formula.
	 * 
	 * @param constraintFormula the abstract sub-constraint to get the smt2
	 *  string representation for
	 * 
	 * @return the smt2 string representation for the given abstract constraint
	 *  formula
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
	
	/**
	 * prepareAbstractPrematureConstraintValue returns the string
	 *  representation of a given abstract premature constraint value.
	 * 
	 * @param prematureConstraintValue the abstract premature constraint value to proceed
	 * 
	 * @return the string representation of the abstract constraint formula
	 */
	public String prepareAbstractPrematureConstraintValue(AbstractPrematureConstraintValue prematureConstraintValue) {
		System.out.println(prematureConstraintValue.toString());
		
		throw new RuntimeException("PREMATURE");
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * getConnectorName returns the smt2 name of the given boolean connector.
	 * 
	 * @param connector the boolean connector
	 * 
	 * @return the smt2 name of the given boolean connector
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
	 * getOperatorOpening returns the start of an expression with the given
	 *  constraint operator.
	 * 
	 * @param operator the constraint operator
	 * 
	 * @return the start of an expression with the given constraint operator
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
	 * getOperatorClosing returns the end of an expression with the given
	 *  constraint operator.
	 * 
	 * @param operator the constraint operator
	 * 
	 * @return the end of an expression with the given constraint operator
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
	 * getVariableDeclaration returns the smt2 representation of a variable
	 *  declaration for the given variable field.
	 * 
	 * @param variableField the variable to get the declaration for
	 * 
	 * @return the smt2 representation of a variable declaration for the given
	 *  variable field
	 */
	private String getVariableDeclaration(VariableField variableField) {
		StringBuilder variableDeclaration = new StringBuilder();
		variableDeclaration.append("(declare-const ");
		variableDeclaration.append(variableField.variableName);
		
		if(variableField.fieldType.equals(Double.class))
			variableDeclaration.append(" Real)");
		else if(variableField.fieldType.equals(Float.class))
			variableDeclaration.append(" Real)");
		else if(variableField.fieldType.equals(Integer.class))
			variableDeclaration.append(" Int)");
		else {
			String message = "could not translate class \"" + variableField.fieldType.getName() + "\" to Z3 syntax.";
			Logger.getLogger(SMTII.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
		
		return variableDeclaration.toString();
	}
}
