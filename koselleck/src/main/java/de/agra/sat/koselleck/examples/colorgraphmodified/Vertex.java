package de.agra.sat.koselleck.examples.colorgraphmodified;

import de.agra.sat.koselleck.annotations.Variable;

public class Vertex {
	public final int id;
	
	@Variable
	public int color;
	
	public int color2;
	
	public Vertex(int id) {
		this.id = id;
	}
}
