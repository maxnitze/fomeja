package de.agra.sat.koselleck.backends;

/** imports */
import java.io.IOException;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.utils.IOUtils;

/**
 * Z3 is an implementation for the z3 theorem prover.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class Z3 implements Prover {
	/** path to the binary file */
	private String pathToBinary;
	
	/**
	 * Constructor for a z3 theorem prover.
	 * 
	 * @param pathToBinary path to the z3 prover binary
	 */
	public Z3(String pathToBinary) {
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
		Process process = null;
		try {
			process = Runtime.getRuntime().exec(this.pathToBinary + " -smt2 -in");
			
			IOUtils.writeToStream(process.getOutputStream(), smt2theorem);
			
			return IOUtils.readFromStream(process.getInputStream());
		} catch (IOException e) {
			String message = "could not execute z3 (\"" + this.pathToBinary + "\") with the given file";
			Logger.getLogger(SMTII.class).fatal(message);
			throw new IllegalArgumentException(message); // TODO other exception type
		} finally {
			if(process != null)
				process.destroy();
		}
	}
}
