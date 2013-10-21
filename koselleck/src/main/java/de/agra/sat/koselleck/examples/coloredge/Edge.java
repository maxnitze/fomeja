package de.agra.sat.koselleck.examples.coloredge;

import de.agra.sat.koselleck.annotations.Variable;

public class Edge {
	public final int v1;
	public final int v2;
	
	@Variable
	public int color;
	
	public Edge(int v1, int v2) {
		this.v1 = v1;
		this.v2 = v2;
	}
}
