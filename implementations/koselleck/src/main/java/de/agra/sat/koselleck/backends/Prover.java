package de.agra.sat.koselleck.backends;

/** imports */
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;

/**
 * Prover is an interface for all possible theorem provers to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Prover {
	/** the dialect of the prover */
	final Dialect dialect;

	/**
	 * Constructor for a new prover.
	 * 
	 * @param dialect the dialect of the new prover
	 */
	public Prover(Dialect dialect) {
		this.dialect = dialect;
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solve solves the given theorem by using the specific prover.
	 * 
	 * @param theorem the theorem to solve
	 * 
	 * @return the solved configuration for the given theorem
	 */
	public abstract String solve(String theorem);

	/** protected methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solveAndAssign solves the theorem given by the single theorems using the
	 *  prover (needs to be an smt2 prover). Afterwards the solved
	 *  configuration is assigned to the parameter object of the theorem.
	 * 
	 * @param component the objects to get the arguments from
	 * @param singleTheorems the single theorems to solve and assign
	 * 
	 * @throws NotSatisfyableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	public void solveAndAssign(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		Theorem theorem = this.dialect.getConstraintForArguments(component, singleTheorems);

		String formattedTheorem = this.dialect.format(theorem);

		System.out.println(formattedTheorem); // TODO delete output formattedTheorem

		String proverResult = this.solve(formattedTheorem);

		System.out.println(proverResult); // TODO delete output proverResult

		Map<String, Object> resultMap = this.dialect.parseResult(proverResult);
		for(Map.Entry<String, ParameterObject> variable : theorem.variablesMap.entrySet()) {
			Object result = resultMap.get(variable.getKey());

			if(result != null) {
				variable.getValue().preField.field.setAccessible(true);
				try {
					variable.getValue().preField.field.set(variable.getValue().object, result);
				} catch (IllegalArgumentException | IllegalAccessException e) {
					String message = "could not access field \"" + variable.getValue().preField.field.getName() +"\"";
					Logger.getLogger(SMTII.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			}
		}
	}
}