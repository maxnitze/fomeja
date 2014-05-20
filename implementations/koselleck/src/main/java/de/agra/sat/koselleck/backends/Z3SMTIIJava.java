package de.agra.sat.koselleck.backends;

import java.util.List;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;

public class Z3SMTIIJava extends Prover<SMTIIJava> {
	/**
	 * 
	 */
	public Z3SMTIIJava() {
		super(new SMTIIJava());
	}

	@Override
	public void solveAndAssign(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfyableException {
		// TODO Auto-generated method stub
	}
}
