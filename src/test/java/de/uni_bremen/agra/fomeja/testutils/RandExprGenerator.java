package de.uni_bremen.agra.fomeja.testutils;

import java.util.Random;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomBooleanExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomEnumExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomVoidExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.NotExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.misc.StoreExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.misc.WildcardBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.misc.WildcardExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremAccessibleObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArrayelementExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArraylengthExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremConstructorExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremFieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremGetfieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremLoopStmtExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremStmtSeqExpr;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class RandExprGenerator {
	/** COMMENT */
	private static final int MAX_DEPTH = 1<<7;

	/** COMMENT */
	private static final Random RANDOMIZER = new Random();

	/* generator methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param exprClass COMMENT
	 * 
	 * @return COMMENT
	 */
	public static <T extends Expression> T generateExpression(Class<T> exprClass) {
		return null;
	}

	/* private inner classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static enum ExpressionClass {
		/* expression classes */
		ArithmeticExpr(ArithmeticExpr.class, Type.GENERAL),
		IfThenElseExpr(IfThenElseExpr.class, Type.GENERAL),
		/* atomar expression classes */
		AtomArrayExpr(AtomArrayExpr.class, Type.ATOMAR),
		AtomBooleanExpr(AtomBooleanExpr.class, Type.ATOMAR),
		AtomCharacterExpr(AtomCharacterExpr.class, Type.ATOMAR),
		AtomClassExpr(AtomClassExpr.class, Type.ATOMAR),
		AtomDoubleExpr(AtomDoubleExpr.class, Type.ATOMAR),
		AtomEnumExpr(AtomEnumExpr.class, Type.ATOMAR),
		AtomFloatExpr(AtomFloatExpr.class, Type.ATOMAR),
		AtomIntegerExpr(AtomIntegerExpr.class, Type.ATOMAR),
		AtomObjectExpr(AtomObjectExpr.class, Type.ATOMAR),
		AtomStringExpr(AtomStringExpr.class, Type.ATOMAR),
		AtomVoidExpr(AtomVoidExpr.class, Type.ATOMAR),
		/* bool expression classes */
		AtomBoolExpr(AtomBoolExpr.class, Type.BOOL),
		BoolIfThenElseExpr(BoolIfThenElseExpr.class, Type.BOOL),
		CompareExpr(CompareExpr.class, Type.BOOL),
		ConnectedBoolExpr(ConnectedBoolExpr.class, Type.BOOL),
		NotExpr(NotExpr.class, Type.BOOL),
		/* misc expression classes */
		StoreExpr(StoreExpr.class, Type.MISC),
		WildcardBoolExpr(WildcardBoolExpr.class, Type.MISC),
		WildcardExpr(WildcardExpr.class, Type.MISC),
		/* premature expression classes */
		PremAccessibleObjectExpr(PremAccessibleObjectExpr.class, Type.PREMATURE),
		PremArrayelementExpr(PremArrayelementExpr.class, Type.PREMATURE),
		PremArraylengthExpr(PremArraylengthExpr.class, Type.PREMATURE),
		PremClasscastExpr(PremClasscastExpr.class, Type.PREMATURE),
		PremConstructorExpr(PremConstructorExpr.class, Type.PREMATURE),
		PremFieldExpr(PremFieldExpr.class, Type.PREMATURE),
		PremGetfieldExpr(PremGetfieldExpr.class, Type.PREMATURE),
		PremLoopStmtExpr(PremLoopStmtExpr.class, Type.PREMATURE),
		PremMethodExpr(PremMethodExpr.class, Type.PREMATURE),
		PremStmtSeqExpr(PremStmtSeqExpr.class, Type.PREMATURE);

		/** COMMENT */
		private static enum Type { GENERAL, ATOMAR, BOOL, MISC, PREMATURE };

		/** COMMENT */
		private static int ATOMAR_COUNT = 0;
		/** COMMENT */
		private static int BOOL_COUNT = 0;

		/* COMMENT */
		static {
				for (ExpressionClass exprClass : values()) {
					if (exprClass.type == Type.ATOMAR)
						++ATOMAR_COUNT;
					else if (exprClass.type == Type.BOOL)
						++BOOL_COUNT;
				}
		}

		/** COMMENT */
		private Class<? extends Expression> cls;
		/** COMMENT */
		private Type type;

		/**
		 * COMMENT
		 * 
		 * @param cls COMMENT
		 * @param type COMMENT
		 */
		ExpressionClass(Class<? extends Expression> cls, Type type) {
			this.cls = cls;
			this.type = type;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public static ExpressionClass getRandAll() {
			return values()[RANDOMIZER.nextInt(values().length)];
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public static ExpressionClass getRandAtomar() {
			int rand = RANDOMIZER.nextInt(ATOMAR_COUNT);

			for (ExpressionClass exprClass : values()) {
				if (exprClass.type == Type.ATOMAR) {
					if (rand == 0)
						return exprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater the amount of atomar types classes!";
			Logger.getLogger(ExpressionClass.class).fatal(message);
			throw new RuntimeException(message);
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public static ExpressionClass getRandBool() {
			int rand = RANDOMIZER.nextInt(BOOL_COUNT);

			for (ExpressionClass exprClass : values()) {
				if (exprClass.type == Type.BOOL) {
					if (rand == 0)
						return exprClass;
					else
						--rand;
				}
			}

			String message = "generated random value greater the amount of bool types classes!";
			Logger.getLogger(ExpressionClass.class).fatal(message);
			throw new RuntimeException(message);
		}
	};
}
