package de.agra.sat.koselleck.backends;

/**
 * Prover is an interface for all possible theorem provers to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public interface Prover {
	/**
	 * solve solves the given theorem by using the specific prover.
	 * 
	 * @param theorem the theorem to solve
	 * 
	 * @return the solved configuration for the given theorem
	 */
	public abstract String solve(String theorem);
}
