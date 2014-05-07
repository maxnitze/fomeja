package de.agra.sat.koselleck.examples.mutualexclusion;

import de.agra.sat.koselleck.annotations.Variable;

public class Access {
	public final int id;

	public final int resource;

	public final int period;

	@Variable
	public int time;

	public Access(int id, int resource, int period) {
		this.id = id;
		this.resource = resource;
		this.period = period;
	}
}
