package de.agra.sat.koselleck.backends;

/** imports */
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ComplexParameterObject;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.SimpleParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;

/**
 * Prover is an interface for all possible theorem provers to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Prover<T extends Dialect<?, ?>> {
	/** the dialect of the prover */
	final T dialect;

	/**
	 * Constructor for a new prover.
	 * 
	 * @param dialect the dialect of the new prover
	 */
	public Prover(T dialect) {
		this.dialect = dialect;
	}

	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solveAndAssign solves the theorem given by the single theorems using the
	 *  prover (needs to be an smt2 prover). Afterwards the solved
	 *  configuration is assigned to the parameter object of the theorem.
	 * 
	 * @param component the objects to get the arguments from
	 * @param singleTheorems the single theorems to solve and assign
	 * 
	 * @throws NotSatisfiableException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	public abstract void solveAndAssign(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfiableException;

	/**
	 * 
	 * @param theorem
	 * @param proverResults
	 */
	void assign(Theorem theorem, Map<String, Object> proverResults) {
		for (Map.Entry<String, ParameterObject> variable : theorem.variablesMap.entrySet()) {
			Object proverResult = proverResults.get(variable.getKey());

			if (proverResult != null) {
				boolean accessibility = variable.getValue().preField.field.isAccessible(); 
				variable.getValue().preField.field.setAccessible(true);
				try {
					if (variable.getValue() instanceof SimpleParameterObject)
						variable.getValue().preField.field.set(variable.getValue().object, proverResult);
					else if (variable.getValue() instanceof ComplexParameterObject) {
						ComplexParameterObject complexParameterObject = (ComplexParameterObject) variable.getValue();
						Object objectRangeElement = complexParameterObject.getObjectRangeElement((Integer) proverResult);
						complexParameterObject.preField.field.set(variable.getValue().object, objectRangeElement);
					}
				} catch (IllegalArgumentException | IllegalAccessException e) {
					String message = "could not access field \"" + variable.getValue().preField.field.getName() +"\"";
					Logger.getLogger(SMTIIString.class).fatal(message);
					throw new IllegalArgumentException(message);
				} finally {
					variable.getValue().preField.field.setAccessible(accessibility);
				}
			}
		}
	}
}