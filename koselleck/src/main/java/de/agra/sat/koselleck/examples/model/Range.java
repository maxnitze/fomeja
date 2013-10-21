package de.agra.sat.koselleck.examples.model;

/**
 * 
 * @author max
 *
 * @param <T>
 */
public class Range<T extends Comparable<T>> {
	/**  */
	public final T start;
	/**  */
	public final T end;
	
	/**
	 * 
	 * @param start
	 * @param end
	 */
	public Range(T start, T end) {
		if(start.compareTo(end) <= 0) {
			this.start = start;
			this.end = end;
		} else {
			this.start = end;
			this.end = start;
		}
	}
	
	/**
	 * 
	 * @param r
	 * 
	 * @return
	 */
	public boolean intersectsWith(Range<T> r) {
		if(this.start.compareTo(r.start) <= 0 && this.end.compareTo(r.start) > 0)
			return true;
		
		if(r.start.compareTo(this.start) <= 0 && r.end.compareTo(this.start) > 0)
			return true;
		
		return false;
	}
}
