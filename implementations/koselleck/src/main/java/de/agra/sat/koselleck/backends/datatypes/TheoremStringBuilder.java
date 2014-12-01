package de.agra.sat.koselleck.backends.datatypes;

import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class TheoremStringBuilder {
	/** COMMENT */
	private Map<String, String> variableDeclarations;
	/** COMMENT */
	private StringBuilder constraints;

	/**
	 * COMMENT
	 */
	public TheoremStringBuilder() {
		this.variableDeclarations = new HashMap<String, String>();
		this.constraints = new StringBuilder();
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param variableDeclaration
	 */
	public void appendVariableDeclaration(String name, String variableDeclaration) {
		if (this.variableDeclarations.get(name) != null) {
			this.variableDeclarations.put(name, variableDeclaration);
			this.constraints.append("\n");
		} else
			Logger.getLogger(TheoremStringBuilder.class).warn("tried to append variable declaration \"" + name + "\" that has already been added");
	}

	/**
	 * COMMENT
	 * 
	 * @param constraint
	 */
	public void appendConstraint(String constraint) {
		this.constraints.append("\t");
		this.constraints.append(constraint);
		this.constraints.append("\n");
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public String toString() {
		StringBuilder theoremString = new StringBuilder();
		theoremString.append(this.variableDeclarations.toString());
		theoremString.append("(assert (and ");
		theoremString.append(this.constraints.toString());
		theoremString.append("))\n(check-sat)\n(get-model)");
		return theoremString.toString();
	}
}
