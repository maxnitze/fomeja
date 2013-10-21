package de.agra.sat.koselleck.examples.colorgraphmodified;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;
import de.agra.sat.koselleck.examples.model.Pair;

@SuppressWarnings("unused")
public class Graph {
	private List<Vertex> vertices;
	private List<Pair<Vertex,Vertex>> edges;
	
	private Pair<Vertex, Vertex> x;
	
	public static Graph parse(String graphFile) throws IllegalArgumentException {
		Vertex vertex1 = new Vertex(1);
		vertex1.color = 1;
		vertex1.color2 = 1;
		Vertex vertex2 = new Vertex(2);
		vertex2.color = 2;
		vertex2.color2 = 2;
		Vertex vertex3 = new Vertex(3);
		vertex3.color = 3;
		vertex3.color2 = 3;
		Vertex vertex4 = new Vertex(4);
		vertex4.color = 4;
		vertex4.color2 = 4;
		Vertex vertex5 = new Vertex(5);
		vertex5.color = 5;
		vertex5.color2 = 5;
		
		List<Pair<Vertex,Vertex>> edges = new ArrayList<Pair<Vertex, Vertex>>();
		edges.add(new Pair<Vertex, Vertex>(vertex1, vertex2));
		edges.add(new Pair<Vertex, Vertex>(vertex1, vertex3));
		edges.add(new Pair<Vertex, Vertex>(vertex1, vertex4));
		edges.add(new Pair<Vertex, Vertex>(vertex1, vertex5));
		edges.add(new Pair<Vertex, Vertex>(vertex2, vertex3));
		edges.add(new Pair<Vertex, Vertex>(vertex2, vertex4));
		edges.add(new Pair<Vertex, Vertex>(vertex2, vertex5));
		edges.add(new Pair<Vertex, Vertex>(vertex3, vertex4));
		edges.add(new Pair<Vertex, Vertex>(vertex3, vertex5));
		edges.add(new Pair<Vertex, Vertex>(vertex4, vertex5));
		
		return new Graph(new ArrayList<Vertex>(), edges);
	}
	
	private Graph(List<Vertex> vertices, List<Pair<Vertex, Vertex>> edges) {
		this.vertices = vertices;
		this.edges = edges;
		
		Vertex v1 = new Vertex(-1);
		v1.color2 = 5;
		Vertex v2 = new Vertex(-1);
		v2.color2 = 5;
		
		this.x = new Pair<Vertex, Vertex>(v1, v2);
	}
	
	@Constraint(fields = @Constraint.Field(name = "vertices"))
	public boolean adjacentHaveDifferentColors(Pair<Vertex,Vertex> e) {
		int x = 60;
		
		switch(x) {
		case 1:
			return e.first.color+1 != e.second.color;
		case 2:
			return e.first.color+2 != e.second.color;
		case 3:
			return e.first.color+3 != e.second.color;
		default:
			return e.first.color != e.second.color;
		}
		
//		boolean b1 = e.first.color != e.second.color;
////		b1 = e.first.color+1 != e.second.color+1;
//		return b1 || x.first.color2 == 6;
	}
	
	@Objective
	public int numberOfColors() {
		Set<Integer> colors = new HashSet<Integer>();
		for(Vertex vertex : this.vertices)
			colors.add(vertex.color);
		
		return colors.size();
	}
}
