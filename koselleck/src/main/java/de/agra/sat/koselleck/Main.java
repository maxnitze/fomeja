package de.agra.sat.koselleck;

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
		graph.parse(IOUtils.readFromFile("/graphs/" + graphfile));
		
		if(testValidate) {
			if(I2AL.validate(graph))
				System.out.println("the current configuration for graph \"" + graphfile + "\" is valid");
			else
				System.out.println("the current configuration for graph \"" + graphfile + "\" is not valid");
		}
		
		if(testSatisfy) {
			if(I2AL.satisfy(graph))
				System.out.println("the graph \"" + graphfile + "\" is satisfyable");
			else
				System.out.println("the graph \"" + graphfile + "\" is not satisfyable");
		}
		
		if(testMinimize) {
			I2AL.minimize(graph);
		}
		
		if(testMaximize) {
			I2AL.maximize(graph);
		}
	}
}
