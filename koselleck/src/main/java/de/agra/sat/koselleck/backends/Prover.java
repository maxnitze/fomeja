package de.agra.sat.koselleck.backends;

/**
 * 
 * @author Max Nitze
 */
public interface Prover {
	/**
	 * 
	 * @param theorem
	 * 
	 * @return
	 */
	public String solve(String theorem);
}
