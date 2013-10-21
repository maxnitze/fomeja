package de.agra.sat.koselleck.examples.coloredge;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;

public class Graph {
	private List<Edge> edges;
	
	@Constraint(fields = { 
			@Constraint.Field(name = "edges"),
			@Constraint.Field(name = "edges")
	})
	public boolean adjacentEdgesHaveDifferentColors(Edge e1, Edge e2) {
		return (e1.v1 != e2.v1 && e1.v1 != e2.v2 && e1.v2 != e2.v1 && e1.v2 != e2.v2) ||
				e1.color != e2.color ||
				e1 == e2;
	}
	
	@Objective
	public int numberOfColors() {
		Set<Integer> colors = new HashSet<Integer>();
		for(Edge edge : this.edges)
			colors.add(edge.color);
		
		return colors.size();
	}
}
