package de.agra.sat.koselleck.backends;

/** imports */
import java.io.IOException;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.ExecutionErrorException;
import de.agra.sat.koselleck.exceptions.UnsupportedDialectTypeException;
import de.agra.sat.koselleck.utils.IOUtils;

/**
 * Z3 is an implementation for the z3 theorem prover.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Z3 extends Prover {
	/** path to the binary file */
	private String pathToBinary;
	
	/**
	 * Constructor for a z3 theorem prover.
	 * 
	 * @param pathToBinary path to the z3 prover binary
	 * @param dialect the dialect to deal with
	 */
	public Z3(String pathToBinary, Dialect dialect) {
		super(dialect);
		this.pathToBinary = pathToBinary;
	}
	
	/**
	 * solve solves the given smt2 theorem by calling the z3 binary given by
	 *  the path with the given smt2 theorem and returns the result, that
	 *  represents the configuration for the theorem.
	 * 
	 * @param smt2theorem the theorem to solve
	 * 
	 * @return a configuration for the theorem
	 */
	@Override
	public String solve(String smt2theorem) {
//		System.out.println(smt2theorem); // TODO delete
		
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
				Logger.getLogger(Z3.class).error("the dialect type \"" + this.dialect.dialectType.name() + "\" is not supported by the z3 theorem prover.");
				throw new UnsupportedDialectTypeException(this.dialect, "z3 theorem prover");
			}
			
			IOUtils.writeToStream(process.getOutputStream(), smt2theorem);
			
			return IOUtils.readFromStream(process.getInputStream());
		} catch (IOException e) {
			String message = "could not execute z3 (\"" + this.pathToBinary + "\") with the given file";
			Logger.getLogger(SMTII.class).fatal(message);
			throw new ExecutionErrorException(message);
		} finally {
			if(process != null)
				process.destroy();
		}
	}
}