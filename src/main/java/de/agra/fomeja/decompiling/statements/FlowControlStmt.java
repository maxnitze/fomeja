package de.agra.fomeja.decompiling.statements;

/* imports */
import de.agra.fomeja.decompiling.misc.ComponentVariables;
import de.agra.fomeja.decompiling.statements.misc.State;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class FlowControlStmt extends Statement {
	@Override
	public abstract FlowControlStmt evaluate(State state, ComponentVariables compVars);
}
