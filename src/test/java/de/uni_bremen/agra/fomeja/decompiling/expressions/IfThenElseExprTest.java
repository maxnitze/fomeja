package de.uni_bremen.agra.fomeja.decompiling.expressions;

import static org.junit.Assert.assertTrue;

import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.testutils.RandElementGenerator;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class IfThenElseExprTest {
	private static IfThenElseExpr ifThenElseExpr1;
	private static IfThenElseExpr ifThenElseExpr2;

	private static IfThenElseExpr genIfThenElseExpr1;
	private static IfThenElseExpr genIfThenElseExpr2;

	@BeforeClass
	public static void setUp() {
		ifThenElseExpr1 = new IfThenElseExpr(
				new CompareExpr(
						new AtomIntegerExpr(0), CompareOperator.EQUAL, new AtomIntegerExpr(1)),
						new AtomIntegerExpr(0), new AtomIntegerExpr(1));
		ifThenElseExpr2 = new IfThenElseExpr(
				new CompareExpr(
						new AtomIntegerExpr(0), CompareOperator.EQUAL, new AtomIntegerExpr(1)),
						new AtomIntegerExpr(0), new AtomIntegerExpr(1));

		genIfThenElseExpr1 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
		genIfThenElseExpr2 = genIfThenElseExpr1.clone();
	}

	@Test
	public void equalsTest() {
		assertTrue("ifThenElseExpr1 must be equal to itself", ifThenElseExpr1.equals(ifThenElseExpr1));
		assertTrue("ifThenElseExpr2 must be equal to itself", ifThenElseExpr2.equals(ifThenElseExpr2));

		assertTrue("genIfThenElseExpr1 must be equal to itself", genIfThenElseExpr1.equals(genIfThenElseExpr1));
		assertTrue("genIfThenElseExpr2 must be equal to itself", genIfThenElseExpr2.equals(genIfThenElseExpr2));

		assertTrue("ifThenElseExpr1 must be equal to ifThenElseExpr2", ifThenElseExpr1.equals(ifThenElseExpr2));
		assertTrue("ifThenElseExpr2 must be equal to ifThenElseExpr1", ifThenElseExpr2.equals(ifThenElseExpr1));

		assertTrue("genIfThenElseExpr1 must be equal to genIfThenElseExpr2", genIfThenElseExpr1.equals(genIfThenElseExpr2));
		assertTrue("genIfThenElseExpr2 must be equal to genIfThenElseExpr1", genIfThenElseExpr2.equals(genIfThenElseExpr1));
	}

	@Test
	public void hashCodeTest() {
		assertTrue("ifThenElseExpr1 and ifThenElseExpr2 are equal, so hashcodes must be same",
				ifThenElseExpr1.equals(ifThenElseExpr2) && ifThenElseExpr1.hashCode() == ifThenElseExpr2.hashCode());
		assertTrue("genIfThenElseExpr1 and genIfThenElseExpr2 are equal, so hashcodes must be same",
				genIfThenElseExpr1.equals(genIfThenElseExpr2) && genIfThenElseExpr1.hashCode() == genIfThenElseExpr2.hashCode());
	}
}
