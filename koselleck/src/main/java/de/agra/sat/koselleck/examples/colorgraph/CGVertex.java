package de.agra.sat.koselleck.examples.colorgraph;

import de.agra.sat.koselleck.annotations.Variable;

public class CGVertex {
	public final int id;
	
	@Variable
	public int color;
	
	public CGVertex(int id) {
		this.id = id;
	}
	
	public int getColor() {
		return this.color;
	}
}
