package de.agra.sat.koselleck.examples.model;

/**
 * 
 * @author max
 *
 * @param <T1>
 * @param <T2>
 */
public class Pair<T1, T2> {
	/**  */
	public final T1 first;
	/**  */
	public final T2 second;
	
	/**
	 * 
	 * @param first
	 * @param second
	 */
	public Pair(T1 first, T2 second) {
		this.first = first;
		this.second = second;
	}
}
