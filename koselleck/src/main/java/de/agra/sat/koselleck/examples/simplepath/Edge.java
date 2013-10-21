package de.agra.sat.koselleck.examples.simplepath;

import de.agra.sat.koselleck.annotations.Variable;

public class Edge {
	public final int v1;
	public final int v2;
	
	@Variable
	public int weight;
	
	public Edge(int v1, int v2) {
		this.v1 = v1;
		this.v2 = v2;
	}
	
	@Override
	public boolean equals(Object object) {
		if(object instanceof Edge || object instanceof EdgeOnPath) {
			Edge edge = (Edge) object;
			if(this.v1 == edge.v1 && this.v1 == edge.v1)
				return true;
			else
				return false;
		} else
			return false;
	}
}
