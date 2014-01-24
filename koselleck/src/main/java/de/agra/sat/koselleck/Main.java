package de.agra.sat.koselleck;

import java.io.IOException;

import de.agra.sat.koselleck.examples.colorgraph.CGGraph;
import de.agra.sat.koselleck.utils.IOUtils;

public class Main {
	public static void main(String[] args) {
		boolean testValidate	= false;
		boolean testSatisfy		= true;
		boolean testMinimize	= false;
		boolean testMaximize	= false;
		
		String graphfile = "fullgraph_20.col";
		CGGraph graph = new CGGraph();
		try {
			graph.parse(IOUtils.readFromFile("/graphs/" + graphfile));
		} catch (IOException e) {
			System.err.println("could not read from file \"graphs/" + graphfile + "\"");
			e.printStackTrace();
		}
		
		if(testValidate) {
			if(DIAB.validate(graph))
				System.out.println("the current configuration for graph \"" + graphfile + "\" is valid");
			else
				System.out.println("the current configuration for graph \"" + graphfile + "\" is not valid");
		}
		
		if(testSatisfy) {
			if(DIAB.satisfy(graph))
				System.out.println("the graph \"" + graphfile + "\" is assigned with a satisfying assignment");
			else
				System.out.println("the graph \"" + graphfile + "\" is not assigned with a satisfying assignment");
		}
		
		if(testMinimize) {
			DIAB.minimize(graph);
		}
		
		if(testMaximize) {
			DIAB.maximize(graph);
		}
	}
}
