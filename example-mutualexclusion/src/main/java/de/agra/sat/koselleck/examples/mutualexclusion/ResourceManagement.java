package de.agra.sat.koselleck.examples.mutualexclusion;

import java.util.List;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Objective;

public class ResourceManagement {
	private List<Access> accesses;
	
	@Constraint(fields = {
			@Constraint.Field("accesses"),
			@Constraint.Field("accesses")
	})
	public boolean noConcurrentAccess(Access a1, Access a2) {
		return
				a1.time+a1.period <= a2.time ||
				a2.time+a2.period <= a1.time ||
				a1.resource != a2.resource ||
				a1 == a2;
	}
	
	@Objective // @Objective(X) / @Objective(value=X) ?
	public int totalAccessTime() {
		int totalAccessTime = 0;
		for(Access access : accesses)
			totalAccessTime += access.time;
		
		return totalAccessTime;
	}
}
