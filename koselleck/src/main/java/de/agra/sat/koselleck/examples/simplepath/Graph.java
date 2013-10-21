package de.agra.sat.koselleck.examples.simplepath;

import java.util.List;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;
import de.agra.sat.koselleck.examples.model.Op;

public class Graph {
	private List<Edge> edges;
	
	private List<EdgeOnPath> path;
	
	// ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
	
	@Constraint(fields = {
			@Constraint.Field(name = "path"),
			@Constraint.Field(name = "path")
	})
	public boolean followingEdgesAreConnected(EdgeOnPath e1, EdgeOnPath e2) {
		return 
				Op.xxor(e1.v1 == e2.v1, e1.v1 == e2.v2, e1.v2 == e2.v1, e1.v2 == e2.v2) ||
				(e1.stepCount+1 != e2.stepCount && e1.stepCount != e2.stepCount+1);
	}
	
	// ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
	
	@Constraint(fields = {
			@Constraint.Field(name = "path"),
			@Constraint.Field(name = "path")
	})
	public boolean noDoubleVisitedVertices(EdgeOnPath e1, EdgeOnPath e2) {
		return
				(e1.v1 != e2.v1 && e1.v1 != e2.v2 && e1.v2 != e2.v1 && e1.v2 == e2.v2) ||
				(Op.xxor(e1.v1 == e2.v1, e1.v1 == e2.v2, e1.v2 == e2.v1, e1.v2 == e2.v2) &&
						(e1.stepCount+1 == e2.stepCount || e1.stepCount == e2.stepCount+1));
	}
	
	// ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
	
	@Constraint(fields = @Constraint.Field(name = "path"))
	public boolean isPathThroughGraph(EdgeOnPath edge) {
		return this.edges.contains(edge);
	}
	
	// ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
	
	@Objective
	public int weightOfWay() {
		int totalWeight = 0;
		for(Edge edge : this.path)
			totalWeight += edge.weight;
		
		return totalWeight;
	}
}
