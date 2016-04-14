package de.uni_bremen.agra.fomeja.decompiling.expressions;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
@RunWith(Parameterized.class)
public class IfThenElseExprTest {
	private IfThenElseExpr ifThenElseExpr1;
	private IfThenElseExpr ifThenElseExpr2;

	public IfThenElseExprTest() {
		this.ifThenElseExpr1 = new IfThenElseExpr(
				new CompareExpr(
						new AtomIntegerExpr(0), CompareOperator.EQUAL, new AtomIntegerExpr(1)),
						new AtomIntegerExpr(0), new AtomIntegerExpr(1));
		this.ifThenElseExpr2 = new IfThenElseExpr(
				new CompareExpr(
						new AtomIntegerExpr(0), CompareOperator.EQUAL, new AtomIntegerExpr(1)),
						new AtomIntegerExpr(0), new AtomIntegerExpr(1));
	}

	@Test
	public void equalsTest() {
		assertTrue("expression must be equal to itself", this.ifThenElseExpr1.equals(this.ifThenElseExpr1));
		assertTrue("expression must be equal to itself", this.ifThenElseExpr2.equals(this.ifThenElseExpr2));

		assertTrue("expressions must be equal", this.ifThenElseExpr1.equals(this.ifThenElseExpr2));
		assertTrue("expressions must be equal", this.ifThenElseExpr2.equals(this.ifThenElseExpr1));
	}

	@Test
	public void hashCodeTest() {
		assertTrue("if expressions are equal hashcode must be same",
				this.ifThenElseExpr1.equals(this.ifThenElseExpr2) ? this.ifThenElseExpr1.hashCode() == this.ifThenElseExpr2.hashCode() : true);
	}
}
