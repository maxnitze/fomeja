package de.uni_bremen.agra.fomeja.decompiling.expressions;

import static org.hamcrest.CoreMatchers.equalTo;
import static org.hamcrest.CoreMatchers.not;
import static org.junit.Assert.assertThat;

import org.junit.Test;

import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.testutils.RandElementGenerator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class IfThenElseExprTest {
	private IfThenElseExpr ifThenElseExprEqual1;
	private IfThenElseExpr ifThenElseExprEqual2;

	private IfThenElseExpr ifThenElseExprSmall1;
	private IfThenElseExpr ifThenElseExprSmall2;

	private IfThenElseExpr ifThenElseExprGen1;
	private IfThenElseExpr ifThenElseExprGen2;
	private IfThenElseExpr ifThenElseExprGen3;
	private IfThenElseExpr ifThenElseExprGen4;
	private IfThenElseExpr ifThenElseExprGen5;


	@Test
	public void equalsTest() {
		/** setup */
		this.setUpEqualExprs();
		this.setUpSmallExprs();

		/** assertions */
		assertThat("if-then-else expressions must be equal to themselves",
				this.ifThenElseExprEqual1, equalTo(this.ifThenElseExprEqual1));
		assertThat("if-then-else expressions must be equal to themselves",
				this.ifThenElseExprEqual2, equalTo(this.ifThenElseExprEqual2));

		assertThat("if-then-else expressions must be equal to themselves",
				this.ifThenElseExprSmall1, equalTo(this.ifThenElseExprSmall1));
		assertThat("if-then-else expressions must be equal to themselves",
				this.ifThenElseExprSmall2, equalTo(this.ifThenElseExprSmall2));

		assertThat("non-equal if-then-else expressions must not be equal to themselves",
				this.ifThenElseExprSmall1, not(equalTo(this.ifThenElseExprSmall2)));
		assertThat("non-equal if-then-else expressions must not be equal to themselves",
				this.ifThenElseExprSmall2, not(equalTo(this.ifThenElseExprSmall1)));

		assertThat("expressions with equal sub-expressions must be equal",
				this.ifThenElseExprEqual1, equalTo(this.ifThenElseExprEqual2));
		assertThat("expressions with equal sub-expressions must be equal",
				this.ifThenElseExprEqual2, equalTo(this.ifThenElseExprEqual1));
	}

	@Test
	public void cloneTest() {
		/** setup */
		this.setUpSmallExprs();
		IfThenElseExpr ifThenElseExprSmall1Cloned = this.ifThenElseExprSmall1.clone();
		IfThenElseExpr ifThenElseExprSmall2Cloned = this.ifThenElseExprSmall2.clone();
		this.setUpGenExprs1To2();
		IfThenElseExpr ifThenElseExprGen1Cloned = this.ifThenElseExprGen1.clone();
		IfThenElseExpr ifThenElseExprGen2Cloned = this.ifThenElseExprGen2.clone();

		/** assertions */
		assertThat("cloned if-then-else expressions must be equal to each other",
				this.ifThenElseExprSmall1, equalTo(ifThenElseExprSmall1Cloned));
		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprSmall1Cloned, equalTo(this.ifThenElseExprSmall1));

		assertThat("cloned if-then-else expressions must be equal to each other",
				this.ifThenElseExprSmall2, equalTo(ifThenElseExprSmall2Cloned));
		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprSmall2Cloned, equalTo(this.ifThenElseExprSmall2));

		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprGen1, equalTo(ifThenElseExprGen1Cloned));
		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprGen1Cloned, equalTo(ifThenElseExprGen1));

		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprGen2, equalTo(ifThenElseExprGen2Cloned));
		assertThat("cloned if-then-else expressions must be equal to each other",
				ifThenElseExprGen2Cloned, equalTo(ifThenElseExprGen2));
	}

	@Test
	public void hashCodeTest() {
		/** setup */
		this.setUpSmallExprs();
		IfThenElseExpr ifThenElseExprSmall1Cloned = this.ifThenElseExprSmall1.clone();
		IfThenElseExpr ifThenElseExprSmall2Cloned = this.ifThenElseExprSmall2.clone();
		this.setUpGenExprs();
		IfThenElseExpr ifThenElseExprGen1Cloned = this.ifThenElseExprGen1.clone();

		/** assertions */
		assertThat("cloned/equal expressions must have the same hashcodes",
				this.ifThenElseExprSmall1.hashCode(), equalTo(ifThenElseExprSmall1Cloned.hashCode()));
		assertThat("cloned/equal expressions must have the same hashcodes",
				this.ifThenElseExprSmall2.hashCode(), equalTo(ifThenElseExprSmall2Cloned.hashCode()));
		assertThat("cloned/equal expressions must have the same hashcodes",
				this.ifThenElseExprGen1.hashCode(), equalTo(ifThenElseExprGen1Cloned.hashCode()));

		assertThat("non-equal expressions must not have the same hashcodes",
				ifThenElseExprSmall1.hashCode(), not(equalTo(ifThenElseExprSmall2.hashCode())));

		if (this.ifThenElseExprGen1.equals(this.ifThenElseExprGen2))
			assertThat("if two arbitrary expressions are equal, their hashcodes must be equal too",
					this.ifThenElseExprGen1.hashCode(), equalTo(this.ifThenElseExprGen2.hashCode()));
		else
			assertThat("if two arbitrary expressions are not equal, their hashcodes must not be equal either",
					this.ifThenElseExprGen1.hashCode(), not(equalTo(this.ifThenElseExprGen2.hashCode())));
		
		if (this.ifThenElseExprGen1.equals(ifThenElseExprGen3))
			assertThat("if two arbitrary expressions are equal, their hashcodes must be equal too",
					this.ifThenElseExprGen1.hashCode(), equalTo(this.ifThenElseExprGen3.hashCode()));
		else
			assertThat("if two arbitrary expressions are not equal, their hashcodes must not be equal either",
					this.ifThenElseExprGen1.hashCode(), not(equalTo(this.ifThenElseExprGen3.hashCode())));
		
		if (this.ifThenElseExprGen1.equals(ifThenElseExprGen4))
			assertThat("if two arbitrary expressions are equal, their hashcodes must be equal too",
					this.ifThenElseExprGen1.hashCode(), equalTo(this.ifThenElseExprGen4.hashCode()));
		else
			assertThat("if two arbitrary expressions are not equal, their hashcodes must not be equal either",
					this.ifThenElseExprGen1.hashCode(), not(equalTo(this.ifThenElseExprGen4.hashCode())));
		
		if (this.ifThenElseExprGen1.equals(this.ifThenElseExprGen5))
			assertThat("if two arbitrary expressions are equal, their hashcodes must be equal too",
					this.ifThenElseExprGen1.hashCode(), equalTo(ifThenElseExprGen5.hashCode()));
		else
			assertThat("if two arbitrary expressions are not equal, their hashcodes must not be equal either",
					this.ifThenElseExprGen1.hashCode(), not(equalTo(ifThenElseExprGen5.hashCode())));
	}

	/** setup methods
	 * ----- ----- ----- ----- */

	/**
	 * COMMENT
	 */
	private void setUpEqualExprs() {
		this.ifThenElseExprEqual1 = new IfThenElseExpr(
				new AtomBoolExpr(true),
				new AtomIntegerExpr(0), new AtomIntegerExpr(1));
		this.ifThenElseExprEqual2 = new IfThenElseExpr(
				new AtomBoolExpr(true),
				new AtomIntegerExpr(0), new AtomIntegerExpr(1));
	}

	/**
	 * COMMENT
	 */
	private void setUpSmallExprs() {
		this.ifThenElseExprSmall1 = new IfThenElseExpr(
				RandElementGenerator.generateBoolExpr(CompareExpr.class, 1),
				RandElementGenerator.generateExpr(Expression.class, 0),
				RandElementGenerator.generateExpr(Expression.class, 0));
		this.ifThenElseExprSmall2 = new IfThenElseExpr(
				RandElementGenerator.generateBoolExpr(BoolIfThenElseExpr.class, 1),
				RandElementGenerator.generateExpr(Expression.class, 0),
				RandElementGenerator.generateExpr(Expression.class, 0));
	}

	/**
	 * COMMENT
	 */
	private void setUpGenExprs() {
		this.setUpGenExprs1To2();
		this.setUpGenExprs3To5();
	}

	/**
	 * COMMENT
	 */
	private void setUpGenExprs1To2() {
		this.ifThenElseExprGen1 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
		this.ifThenElseExprGen2 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
	}

	/**
	 * COMMENT
	 */
	private void setUpGenExprs3To5() {
		this.ifThenElseExprGen3 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
		this.ifThenElseExprGen4 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
		this.ifThenElseExprGen5 = RandElementGenerator.generateExpr(IfThenElseExpr.class);
	}
}
