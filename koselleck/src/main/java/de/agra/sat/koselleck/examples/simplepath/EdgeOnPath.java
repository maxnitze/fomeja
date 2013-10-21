package de.agra.sat.koselleck.examples.simplepath;

public class EdgeOnPath extends Edge {
	public final int stepCount;
	
	public EdgeOnPath(int v1, int v2, int stepCount) {
		super(v1, v2);
		this.stepCount = stepCount;
	}
	
	@Override
	public boolean equals(Object object) {
		if(object instanceof EdgeOnPath) {
			EdgeOnPath edge = (EdgeOnPath) object;
			if(this.v1 == edge.v1 && this.v1 == edge.v1 && this.stepCount == edge.stepCount)
				return true;
			else
				return false;
		} else if(object instanceof Edge) {
			Edge edge = (Edge) object;
			if(this.v1 == edge.v1 && this.v1 == edge.v1)
				return true;
			else
				return false;
		} else
			return false;
	}
}
