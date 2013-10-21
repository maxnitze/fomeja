package de.agra.sat.koselleck.examples.colorgraph;

import edu.uci.ics.jung.graph.util.EdgeType;

public class CGEdge {
	public final CGVertex vertex1;
	public final CGVertex vertex2;
	public final EdgeType edgeType;
	
	public CGEdge(CGVertex vertex1, CGVertex vertex2) {
		this.vertex1 = vertex1;
		this.vertex2 = vertex2;
		this.edgeType = EdgeType.UNDIRECTED;
	}
	
	public CGEdge(CGVertex vertex1, CGVertex vertex2, EdgeType edgeType) {
		this.vertex1 = vertex1;
		this.vertex2 = vertex2;
		this.edgeType = edgeType;
	}
}
