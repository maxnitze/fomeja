package de.agra.sat.koselleck.backends;

/** imports */
import java.io.IOException;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ParameterObject;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.exceptions.ExecutionErrorException;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;
import de.agra.sat.koselleck.exceptions.UnsupportedDialectTypeException;
import de.agra.sat.koselleck.utils.IOUtils;

/**
 * Z3 is an implementation for the z3 theorem prover.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Z3SMTIIBinary extends Prover<SMTIIString> {
	/** path to the binary file */
	private String pathToBinary;

	/**
	 * Constructor for a z3 theorem prover.
	 * 
	 * @param pathToBinary path to the z3 prover binary
	 */
	public Z3SMTIIBinary(String pathToBinary) {
		super(new SMTIIString());
		this.pathToBinary = pathToBinary;
	}

	@Override
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
					Logger.getLogger(SMTIIString.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
			}
		}
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solve solves the given smt2 theorem by calling the z3 binary given by
	 *  the path with the given smt2 theorem and returns the result, that
	 *  represents the configuration for the theorem.
	 * 
	 * @param smt2theorem the theorem to solve
	 * 
	 * @return a configuration for the theorem
	 */
	private String solve(String smt2theorem) {
		Process process = null;
		try {
			switch(this.dialect.dialectType) {
			case smt:
				process = Runtime.getRuntime().exec(this.pathToBinary + " -smt -in");
				break;
			case smt2:
				process = Runtime.getRuntime().exec(this.pathToBinary + " -smt2 -in");
				break;
			case dl:
				process = Runtime.getRuntime().exec(this.pathToBinary + " -dl -in");
				break;
			case dimacs:
				process = Runtime.getRuntime().exec(this.pathToBinary + " -dimacs -in");
				break;
			default:
				Logger.getLogger(Z3SMTIIBinary.class).error("the dialect type \"" + this.dialect.dialectType.name() + "\" is not supported by the z3 theorem prover.");
				throw new UnsupportedDialectTypeException(this.dialect, "z3 theorem prover");
			}

			IOUtils.writeToStream(process.getOutputStream(), smt2theorem);

			return IOUtils.readFromStream(process.getInputStream());
		} catch (IOException e) {
			String message = "could not execute z3 (\"" + this.pathToBinary + "\") with the given file";
			Logger.getLogger(SMTIIString.class).fatal(message);
			throw new ExecutionErrorException(message);
		} finally {
			if(process != null)
				process.destroy();
		}
	}
}