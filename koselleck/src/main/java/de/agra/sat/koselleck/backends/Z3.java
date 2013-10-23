package de.agra.sat.koselleck.backends;

import java.io.IOException;
import java.io.OutputStream;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.utils.IOUtils;

/**
 * 
 * @author Max Nitze
 */
public class Z3 implements Prover {
	/**
	 * 
	 * @param smt2theorem
	 * 
	 * @return
	 */
	@Override
	public String solve(String smt2theorem) {
		Process process = null;
		try {
			process = Runtime.getRuntime().exec("z3 -smt2 -in");
			OutputStream outputStream = process.getOutputStream();
			IOUtils.writeToOutputStream(outputStream, smt2theorem);
			outputStream.flush();
			
			return IOUtils.readFromStream(process.getInputStream());
		} catch (IOException e) {
			String message = "could not execute z3 with the given file";
			Logger.getLogger(SMTII.class).fatal(message);
			throw new IllegalArgumentException(message); // TODO other exception type
		} finally {
			if(process != null)
				process.destroy();
		}
	}
}
