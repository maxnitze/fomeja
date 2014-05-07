package de.agra.sat.koselleck.datatypes;

/**
 * Pair describes a pair of two given types.
 * 
 * @version 1.0.0
 * @author Max Nitze
 *
 * @param <T1> the first type of the pair
 * @param <T2> the second type of the pair
 */
public class Pair<T1, T2> {
	/** the first object of type T1 of the pair */
	public T1 first;
	/** the second object of type T2 of the pair */
	public T2 second;

	/**
	 * Constructor for a new pair.
	 * 
	 * @param first the new first object
	 * @param second the new second object
	 */
	public Pair(T1 first, T2 second) {
		this.first = first;
		this.second = second;
	}
}
