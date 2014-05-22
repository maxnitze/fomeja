package de.agra.sat.koselleck.examples;

import de.agra.sat.koselleck.DIAB;

public class MutualExclusion {
	public static void main(String[] args) {
		boolean testValidate	= false;
		boolean testSatisfy		= false;
		boolean testMinimize	= false;
		boolean testMaximize	= false;

		Object obj = new Object();
		// prepare Object

		if (testValidate) {
			DIAB.validate(obj);
		}

		if (testSatisfy) {
			DIAB.satisfy(obj);
		}

		if (testMinimize) {
			DIAB.minimize(obj);
		}

		if (testMaximize) {
			DIAB.maximize(obj);
		}
	}
}
