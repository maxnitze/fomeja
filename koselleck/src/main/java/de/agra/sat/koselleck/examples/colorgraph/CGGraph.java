package de.agra.sat.koselleck.examples.colorgraph;

/** imports */
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.graph.util.Pair;

/**
 * 
 * @author Max Nitze
 */
public class CGGraph implements Graph<CGVertex, CGEdge> {
	private static final String commentLine = "^c\\s+.*$";
	private static final String pLine = "^p\\s+edge\\s+(\\d+)\\s+(\\d+)$";
	private static final String edgeLine = "^e\\s+(?<vertex1>\\d+)\\s+(?<vertex2>\\d+)$";
	
	public final Collection<CGVertex> vertices;
	public final Collection<CGEdge> edges;

	public CGGraph() {
		this.vertices = new ArrayList<CGVertex>();
		this.edges = new ArrayList<CGEdge>();
	}
	
	public void parse(String graph) {
		this.vertices.clear();
		this.edges.clear();
		
		Map<Integer, CGVertex> verticesMap = new HashMap<Integer, CGVertex>();
		CGVertex firstVertex = null;
		CGVertex secondVertex = null;
		
		String[] graphLines = graph.split("\n");
		for(String graphLine : graphLines) {
			if(graphLine.matches(commentLine))
				; // skip
			else if(graphLine.matches(pLine))
				; // skip
			else if(graphLine.matches(edgeLine)) {
				int firstVertexId = Integer.parseInt(graphLine.replaceAll(edgeLine, "${vertex1}"));
				if((firstVertex = verticesMap.get(firstVertexId)) == null) {
					firstVertex = new CGVertex(firstVertexId);
					verticesMap.put(firstVertexId, firstVertex);
					this.vertices.add(firstVertex);
				}
				
				int secondVertexId = Integer.parseInt(graphLine.replaceAll(edgeLine, "${vertex2}"));
				if((secondVertex = verticesMap.get(secondVertexId)) == null) {
					secondVertex = new CGVertex(secondVertexId);
					verticesMap.put(secondVertexId, secondVertex);
					this.vertices.add(secondVertex);
				}
				
				this.edges.add(new CGEdge(firstVertex, secondVertex));
			}
		}
	}
	
	@Constraint(fields = { @Constraint.Field(name = "") })
	public boolean adjacentHaveDifferentColors(CGEdge edge) {
		return edge.vertex1.color != edge.vertex2.color;
	}
	
	@Objective
	public int numberOfColors() {
		Collection<Integer> colors = new HashSet<Integer>();
		for(CGVertex v : this.vertices)
			colors.add(v.color);
		
		return colors.size();
	}
	
	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Collection<CGEdge> getEdges() {
		return this.edges;
	}

	@Override
	public Collection<CGVertex> getVertices() {
		return this.vertices;
	}

	@Override
	public boolean containsVertex(CGVertex vertex) {
		return this.vertices.contains(vertex);
	}

	@Override
	public boolean containsEdge(CGEdge edge) {
		return this.edges.contains(edge);
	}

	@Override
	public int getEdgeCount() {
		return this.edges.size();
	}

	@Override
	public int getVertexCount() {
		return this.vertices.size();
	}

	@Override
	public Collection<CGVertex> getNeighbors(CGVertex vertex) {
		Collection<CGVertex> neighbors = new HashSet<CGVertex>();
		
		for(CGEdge e : this.edges) {
			if(e.vertex1 == vertex)
				neighbors.add(e.vertex2);
			if(e.vertex2 == vertex)
				neighbors.add(e.vertex1);
		}
		
		return neighbors;
	}

	@Override
	public Collection<CGEdge> getIncidentEdges(CGVertex vertex) {
		Collection<CGEdge> incidentEdges = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges)
			if(e.vertex1 == vertex || e.vertex2 == vertex)
				incidentEdges.add(e);
		
		return incidentEdges;
	}

	@Override
	public Collection<CGVertex> getIncidentVertices(CGEdge edge) {
		Collection<CGVertex> incidentVertices = new HashSet<CGVertex>();
		
		incidentVertices.add(edge.vertex1);
		incidentVertices.add(edge.vertex2);
		
		return incidentVertices;
	}

	@Override
	public CGEdge findEdge(CGVertex v1, CGVertex v2) {
		for(CGEdge e : this.edges)
			if((e.vertex1 == v1 && e.vertex2 == v2) || (e.vertex1 == v2 && e.vertex2 == v1))
				return e;
		
		return null;
	}

	@Override
	public Collection<CGEdge> findEdgeSet(CGVertex v1, CGVertex v2) {
		Collection<CGEdge> edgeSet = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges)
			if((e.vertex1 == v1 && e.vertex2 == v2) || (e.vertex1 == v2 && e.vertex2 == v1))
				edgeSet.add(e);
		
		return edgeSet;
	}

	@Override
	public boolean addVertex(CGVertex vertex) {
		return this.vertices.add(vertex);
	}

	@Override
	public boolean addEdge(CGEdge edge, Collection<? extends CGVertex> vertices) {
		if(edge == null || vertices == null)
			return false;
		
		if(this.edges.contains(edge))
			return false;
		
		if(vertices.size() != 2)
			return false;
		
		for(CGVertex v : vertices)
			if(!this.vertices.contains(v))
				return false;
		
		for(CGEdge e : this.edges)
			if(edge.equals(e))
				return false;
		
		return this.edges.add(edge);
	}

	@Override
	public boolean addEdge(CGEdge edge, Collection<? extends CGVertex> vertices, EdgeType edge_type) {
		if(edge.edgeType != edge_type)
			return false;
		
		return addEdge(edge, vertices);
	}

	@Override
	public boolean removeVertex(CGVertex vertex) {
		Collection<CGEdge> removeEdges = new HashSet<CGEdge>();
		for(CGEdge e : this.edges)
			if(e.vertex1 == vertex || e.vertex2 == vertex)
				removeEdges.add(e);
		
		return this.edges.removeAll(removeEdges) || this.vertices.remove(vertex);
	}

	@Override
	public boolean removeEdge(CGEdge edge) {
		return this.edges.remove(edge);
	}

	@Override
	public boolean isNeighbor(CGVertex v1, CGVertex v2) {
		for(CGEdge e : this.edges)
			if((e.vertex1 == v1 && e.vertex2 == v2) || (e.vertex1 == v2 && e.vertex2 == v1))
				return true;
		
		return false;
	}

	@Override
	public boolean isIncident(CGVertex vertex, CGEdge edge) {
		return edge.vertex1 == vertex || edge.vertex2 == vertex;
	}

	@Override
	public int degree(CGVertex vertex) {
		int degree = 0;
		
		for(CGEdge e : this.edges)
			if(e.vertex1 == vertex || e.vertex2 == vertex)
				++degree;
		
		return degree;
	}

	@Override
	public int getNeighborCount(CGVertex vertex) {
		int neighborCount = 0;
		
		for(CGEdge e : this.edges)
			if(e.vertex1 == vertex || e.vertex2 == vertex)
				++neighborCount;
		
		return neighborCount;
	}

	@Override
	public int getIncidentCount(CGEdge edge) {
		return 2;
	}

	@Override
	public EdgeType getEdgeType(CGEdge edge) {
		return edge.edgeType;
	}

	@Override
	public EdgeType getDefaultEdgeType() {
		return EdgeType.UNDIRECTED;
	}

	@Override
	public Collection<CGEdge> getEdges(EdgeType edge_type) {
		Collection<CGEdge> edgeTypeEdges = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges)
			if(e.edgeType == edge_type)
				edgeTypeEdges.add(e);
		
		return edgeTypeEdges;
	}

	@Override
	public int getEdgeCount(EdgeType edge_type) {
		Collection<CGEdge> edgeTypeEdges = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges)
			if(e.edgeType == edge_type)
				edgeTypeEdges.add(e);
		
		return edgeTypeEdges.size();
	}

	@Override
	public Collection<CGEdge> getInEdges(CGVertex vertex) {
		Collection<CGEdge> inEdges = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges) {
			if(e.edgeType == EdgeType.DIRECTED) {
				if(e.vertex2 == vertex)
					inEdges.add(e);
			} else if(e.edgeType == EdgeType.UNDIRECTED) {
				if(e.vertex1 == vertex || e.vertex2 == vertex)
					inEdges.add(e);
			}
		}
		
		return inEdges;
	}

	@Override
	public Collection<CGEdge> getOutEdges(CGVertex vertex) {
		Collection<CGEdge> outEdges = new HashSet<CGEdge>();
		
		for(CGEdge e : this.edges) {
			if(e.edgeType == EdgeType.DIRECTED) {
				if(e.vertex1 == vertex)
					outEdges.add(e);
			} else if(e.edgeType == EdgeType.UNDIRECTED) {
				if(e.vertex1 == vertex || e.vertex2 == vertex)
					outEdges.add(e);
			}
		}
		
		return outEdges;
	}

	@Override
	public Collection<CGVertex> getPredecessors(CGVertex vertex) {
		Collection<CGVertex> predecessors = new HashSet<CGVertex>();
		
		for(CGEdge e : this.edges)
			if(e.edgeType == EdgeType.DIRECTED)
				if(e.vertex2 == vertex)
					predecessors.add(e.vertex1);
		
		return predecessors;
	}

	@Override
	public Collection<CGVertex> getSuccessors(CGVertex vertex) {
		Collection<CGVertex> successors = new HashSet<CGVertex>();
		
		for(CGEdge e : this.edges)
			if(e.edgeType == EdgeType.DIRECTED)
				if(e.vertex1 == vertex)
					successors.add(e.vertex2);
		
		return successors;
	}

	@Override
	public int inDegree(CGVertex vertex) {
		return getInEdges(vertex).size();
	}

	@Override
	public int outDegree(CGVertex vertex) {
		return getOutEdges(vertex).size();
	}

	@Override
	public boolean isPredecessor(CGVertex v1, CGVertex v2) {
		for(CGEdge e : this.edges)
			if(e.edgeType == EdgeType.DIRECTED)
				if(e.vertex1 == v1 && e.vertex2 == v2)
					return true;
		
		return false;
	}

	@Override
	public boolean isSuccessor(CGVertex v1, CGVertex v2) {
		for(CGEdge e : this.edges)
			if(e.edgeType == EdgeType.DIRECTED)
				if(e.vertex1 == v2 && e.vertex2 == v1)
					return true;
		
		return false;
	}

	@Override
	public int getPredecessorCount(CGVertex vertex) {
		return getPredecessors(vertex).size();
	}

	@Override
	public int getSuccessorCount(CGVertex vertex) {
		return getSuccessors(vertex).size();
	}

	@Override
	public CGVertex getSource(CGEdge directed_edge) {
		if(directed_edge.edgeType != EdgeType.DIRECTED)
			return null;
		
		return directed_edge.vertex1;
	}

	@Override
	public CGVertex getDest(CGEdge directed_edge) {
		if(directed_edge.edgeType != EdgeType.DIRECTED)
			return null;
		
		return directed_edge.vertex2;
	}

	@Override
	public boolean isSource(CGVertex vertex, CGEdge edge) {
		if(edge.edgeType != EdgeType.DIRECTED)
			return false;
		
		return edge.vertex1 == vertex;
	}

	@Override
	public boolean isDest(CGVertex vertex, CGEdge edge) {
		if(edge.edgeType != EdgeType.DIRECTED)
			return false;
		
		return edge.vertex2 == vertex;
	}

	@Override
	public boolean addEdge(CGEdge e, CGVertex v1, CGVertex v2) {
		return addEdge(e, new Pair<CGVertex>(v1, v2));
	}

	@Override
	public boolean addEdge(CGEdge e, CGVertex v1, CGVertex v2, EdgeType edgeType) {
		return addEdge(e, new Pair<CGVertex>(v1, v2), edgeType);
	}

	@Override
	public Pair<CGVertex> getEndpoints(CGEdge edge) {
		return new Pair<CGVertex>(edge.vertex1, edge.vertex2);
	}

	@Override
	public CGVertex getOpposite(CGVertex vertex, CGEdge edge) {
		if(edge.vertex1 == vertex)
			return edge.vertex2;
		else if(edge.vertex2 == vertex)
			return edge.vertex1;
		else
			return null;
	}
}
