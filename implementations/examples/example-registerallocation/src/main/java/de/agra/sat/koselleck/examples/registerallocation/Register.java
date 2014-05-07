package de.agra.sat.koselleck.examples.registerallocation;

import de.agra.sat.koselleck.annotations.Variable;

class Register {
	public final String name;
	public final Range<Integer> interval;

	@Variable
	public int address;

	public Register(String name, Integer start, Integer end) {
		this.name = name;
		this.interval = new Range<Integer>(start, end);
	}

	class Range<T extends Comparable<T>> {
		public final T start;
		public final T end;

		public Range(T start, T end) {
			this.start = start;
			this.end = end;
		}

		public boolean intersectsWith(Range<T> range) {
			return
					(this.start.compareTo(range.start) < 0 && this.end.compareTo(range.start) >= 0) ||
					(this.end.compareTo(range.end) > 0 && this.start.compareTo(range.end) <= 0) ||
					(this.start.compareTo(range.start) >= 0 && this.end.compareTo(range.end) <= 0) ||
					(this.start.compareTo(range.start) <= 0 && this.end.compareTo(range.end) >= 0);
		}
	}
}
