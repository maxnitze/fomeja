package de.agra.sat.koselleck.examples.register;

import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.examples.model.Range;

class Register {
	public final String name;
	public final Range<Integer> interval;
	
	@Variable
	public int address;
	
	public Register(String name, Integer start, Integer end) {
		this.name = name;
		this.interval = new Range<Integer>(start, end);
	}
}
