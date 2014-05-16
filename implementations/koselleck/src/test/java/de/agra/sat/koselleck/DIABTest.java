package de.agra.sat.koselleck;

/** imports */
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.BeforeClass;
import org.junit.Test;

import de.agra.sat.koselleck.util.VariableInteger;
import de.agra.sat.koselleck.util.VariableIntegers;

/**
 * 
 * @author Max Nitze
 */
public class DIABTest {
	/**  */
	private static VariableIntegers satisfiableVariableIntegers;
	/**  */
	private static VariableIntegers notSatisfiableVariableIntegers;

	@BeforeClass
	public static void setUpBeforeClass() {
		VariableInteger variableInteger;

		Set<VariableInteger> satisfiableSet = new HashSet<VariableInteger>();
		for (int i = 0; i < 10; i++) {
			variableInteger = new VariableInteger();
			variableInteger.integerValue = i;
			satisfiableSet.add(variableInteger);
		}

		satisfiableVariableIntegers = new VariableIntegers(satisfiableSet);

		Set<VariableInteger> notSatisfiableSet = new HashSet<VariableInteger>();
		for (int i = 0; i < 10; i++) {
			variableInteger = new VariableInteger();
			variableInteger.integerValue = 1;
			notSatisfiableSet.add(variableInteger);
		}

		notSatisfiableVariableIntegers = new VariableIntegers(notSatisfiableSet);
	}

	@Test
	public void testSatisfiableVariableIntegers() {
		boolean isSatisfiable = DIAB.validate(satisfiableVariableIntegers);

		assertTrue(isSatisfiable);
	}

	@Test
	public void testNotSatisfiableVariableIntegers() {
		boolean isSatisfiable = DIAB.validate(notSatisfiableVariableIntegers);

		assertFalse(isSatisfiable);
	}
}
