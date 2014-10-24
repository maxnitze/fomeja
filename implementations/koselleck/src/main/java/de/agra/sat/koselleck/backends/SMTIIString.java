package de.agra.sat.koselleck.backends;

/** imports */
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.backends.datatypes.VariableField;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractBooleanConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractIfThenElseConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractNotConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSingleConstraint;
import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractSubConstraint;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintFormula;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteral;
import de.agra.sat.koselleck.exceptions.UnknownBooleanConnectorException;
import de.agra.sat.koselleck.exceptions.UnknownConstraintOperatorException;
import de.agra.sat.koselleck.exceptions.UnsupportedVariableTypeException;
import de.agra.sat.koselleck.types.BooleanConnector;
import de.agra.sat.koselleck.types.ConstraintOperator;
import de.agra.sat.koselleck.utils.CompareUtils;

/**
 * SMTII implements the smt2 pseudo boolean dialect.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class SMTIIString extends Dialect<String, String> {
	/** pattern for a smt2 result constant (function without parameters) */
	private static final Pattern smt2ResultPattern = Pattern.compile("\\(define-fun (?<name>\\S+) \\(\\) (?<type>\\S+)(\n)?\\s*\\(?(?<value>(- \\d+|\\d+))\\)?");

	/**
	 * Constructor for a new SMTII dialect.
	 */
	public SMTIIString() {
		super(Dialect.Type.smt2);
	}

	@Override
	public String format(Theorem theorem) {
		StringBuilder assignedConstraint = new StringBuilder();
		for (AbstractConstraint theoremConstraint : theorem.getAbstractConstraint()) {
			String z3Constraint = this.getBackendConstraint(theoremConstraint);

			assignedConstraint.append("\n\t");
			assignedConstraint.append(z3Constraint);
		}

		StringBuilder smt2theorem = new StringBuilder();
		for (VariableField prefixedVariable : theorem.getVariables()) {
			smt2theorem.append(this.getVariableDeclaration(prefixedVariable));
			smt2theorem.append("\n");
		}
		smt2theorem.append("(assert (and ");
		smt2theorem.append(assignedConstraint.toString());
		smt2theorem.append("\n))\n(check-sat)\n(get-model)");

		return smt2theorem.toString();
	}

	@Override
	public Map<String, Object> parseResult(Object resultObject) {
		if (resultObject instanceof String) {
			String result = (String) resultObject;

			Map<String, Object> resultMap = new HashMap<String, Object>();

			Matcher resultMatcher = smt2ResultPattern.matcher(result);
			while (resultMatcher.find()) {
				if (resultMatcher.group("type").equals("Int"))
					resultMap.put(
							resultMatcher.group("name"),
							new Integer(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
				else if (resultMatcher.group("type").equals("Real"))
					resultMap.put(
							resultMatcher.group("name"),
							new Float(resultMatcher.group("value").replaceAll("- (\\d+)", "-$1")));
				else {
					Logger.getLogger(SMTIIString.class).fatal("could not translate type \"" + resultMatcher.group("type") + "\" to Z3 syntax.");
					throw new UnsupportedVariableTypeException(resultMatcher.group("type"));
				}
			}

			return resultMap;
		} else {
			String message = "could not parse result of type \"" + resultObject.getClass().getCanonicalName() + "\"; only String supported";
			Logger.getLogger(SMTIIString.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
	}

	/** abstract constraints
	 * ----- ----- ----- ----- ----- */

	@Override
	public String prepareAbstractBooleanConstraint(AbstractBooleanConstraint booleanConstraint) {
		return booleanConstraint.getValue() ? "True" : "False";
	}

	@Override
	public String prepareAbstractNotConstraint(AbstractNotConstraint notConstraint) {
		StringBuilder notConstraintString = new StringBuilder();

		notConstraintString.append("(not ");
		notConstraintString.append(this.getBackendConstraint(notConstraint.getConstraint()));
		notConstraintString.append(")");

		return notConstraintString.toString();
	}

	@Override
	public String prepareAbstractSingleConstraint(AbstractSingleConstraint singleConstraint) {
		StringBuilder singleConstraintString = new StringBuilder();

		singleConstraintString.append(this.getOperatorOpening(singleConstraint.getOperator()));
		singleConstraintString.append(" ");
		singleConstraintString.append(this.getBackendConstraintValue(singleConstraint.getValue1()));
		singleConstraintString.append(" ");
		singleConstraintString.append(this.getBackendConstraintValue(singleConstraint.getValue2()));
		singleConstraintString.append(this.getOperatorClosing(singleConstraint.getOperator()));

		return singleConstraintString.toString();
	}

	@Override
	public String prepareAbstractSubConstraint(AbstractSubConstraint subConstraint) {
		StringBuilder subConstraintString = new StringBuilder();

		subConstraintString.append("(");
		subConstraintString.append(this.getConnectorName(subConstraint.getConnector()));
		subConstraintString.append(" ");
		subConstraintString.append(this.getBackendConstraint(subConstraint.getConstraint1()));
		subConstraintString.append(" ");
		subConstraintString.append(this.getBackendConstraint(subConstraint.getConstraint2()));
		subConstraintString.append(")");

		return subConstraintString.toString();
	}

	@Override
	public String prepareAbstractIfThenElseConstraint(AbstractIfThenElseConstraint ifThenElseConstraint) {
		StringBuilder ifThenElseConstraintString = new StringBuilder();

		ifThenElseConstraintString.append("(or (and ");
		ifThenElseConstraintString.append(this.getBackendConstraint(ifThenElseConstraint.getIfCondition()));
		ifThenElseConstraintString.append(" ");
		ifThenElseConstraintString.append(this.getBackendConstraint(ifThenElseConstraint.getThenCaseConstraint()));
		ifThenElseConstraintString.append(") (and (not ");
		ifThenElseConstraintString.append(this.getBackendConstraint(ifThenElseConstraint.getIfCondition()));
		ifThenElseConstraintString.append(") ");
		ifThenElseConstraintString.append(this.getBackendConstraint(ifThenElseConstraint.getElseCaseConstraint()));
		ifThenElseConstraintString.append("))");

		return ifThenElseConstraintString.toString();
	}

	/** abstract constraint values
	 * ----- ----- ----- ----- ----- */

	@Override
	public String prepareAbstractConstraintLiteral(AbstractConstraintLiteral<?> constraintLiteral) {
		return constraintLiteral.toString();
	}

	@Override
	public String prepareAbstractConstraintFormula(AbstractConstraintFormula constraintFormula) {
		StringBuilder constraintFormulaString = new StringBuilder();

		constraintFormulaString.append("(");
		constraintFormulaString.append(constraintFormula.getOperator().getAsciiName());
		constraintFormulaString.append(" ");
		constraintFormulaString.append(this.getBackendConstraintValue(constraintFormula.getValue1()));
		constraintFormulaString.append(" ");
		constraintFormulaString.append(this.getBackendConstraintValue(constraintFormula.getValue2()));
		constraintFormulaString.append(")");

		return constraintFormulaString.toString();
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
			Logger.getLogger(SMTIIString.class).fatal("boolean connector " + (connector == null ? "null" : "\"" + connector.getCode() + "\"") + " is not known");
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
			Logger.getLogger(SMTIIString.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
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
			Logger.getLogger(SMTIIString.class).fatal("constraint operator " + (operator == null ? "null" : "\"" + operator.getAsciiName() + "\"") + " is not known");
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
		variableDeclaration.append(variableField.getVariableName());

		if (CompareUtils.equalsAny(variableField.getFieldType(), CompareUtils.integerClasses))
			variableDeclaration.append(" Int)");
		else if (CompareUtils.equalsAny(variableField.getFieldType(), CompareUtils.floatClasses))
			variableDeclaration.append(" Real)");
		else if (CompareUtils.equalsAny(variableField.getFieldType(), CompareUtils.doubleClasses))
			variableDeclaration.append(" Real)");
		else {
			String message = "could not translate class \"" + variableField.getFieldType().getName() + "\" to Z3 syntax.";
			Logger.getLogger(SMTIIString.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		return variableDeclaration.toString();
	}
}
