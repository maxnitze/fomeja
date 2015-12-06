package de.agra.fomeja.backends;

/* imports */
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.fomeja.backends.datatypes.ResultModel;
import de.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.NotExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremAccessibleObjectExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.agra.fomeja.exceptions.DialectException;
import de.agra.fomeja.exceptions.SatisfyException;
import de.agra.fomeja.utils.CompareUtils;
import de.agra.fomeja.utils.RefactoringUtils;

/**
 * Dialect is an interface for all possible pseudo boolean dialects to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Dialect<T, V> {
	/** COMMENT*/
	private static final Method[] preparableIntegerValueMethods = new Method[] {
		RefactoringUtils.getMethodForClass(Integer.class, "intValue"),
		RefactoringUtils.getMethodForClass(Float.class, "intValue"),
		RefactoringUtils.getMethodForClass(Double.class, "intValue")
	};

	/** COMMENT*/
	private static final Method[] preparableFloatValueMethods = new Method[] {
		RefactoringUtils.getMethodForClass(Integer.class, "intValue"),
		RefactoringUtils.getMethodForClass(Float.class, "intValue"),
		RefactoringUtils.getMethodForClass(Double.class, "intValue")
	};

	/** COMMENT*/
	private static final Method[] preparableDoubleValueMethods = new Method[] {
		RefactoringUtils.getMethodForClass(Integer.class, "intValue"),
		RefactoringUtils.getMethodForClass(Float.class, "intValue"),
		RefactoringUtils.getMethodForClass(Double.class, "intValue")
	};

	/** dialect types */
	public static enum Type {
		smt,
		smt2,
		dl,
		dimacs
	};

	/** dialect type */
	private Dialect.Type dialectType;

	/** COMMENT */
	private List<BoolExpression> extraExprs;

	/**
	 * Constructor for a new dialect.
	 * 
	 * @param dialectType the type of the dialect
	 */
	public Dialect(Dialect.Type dialectType) {
		this.dialectType = dialectType;

		this.extraExprs = new ArrayList<BoolExpression>();
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public Dialect.Type getDialectType() {
		return this.dialectType;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExprs
	 * 
	 * @return
	 * 
	 * @throws SatisfyException
	 */
	public abstract List<T> format(List<BoolExpression> boolExprs) throws SatisfyException;

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param resultObject
	 * 
	 * @return
	 */
	public abstract ResultModel parseResult(Object resultObject);

	/* boolean expressions
	 * ----- ----- ----- ----- ----- */

	/**
	 * prepareAtomBoolExpr returns the dialect specific representation of a
	 *  given atomar boolean expression.
	 * 
	 * @param expr the atomar boolean expression to proceed
	 * 
	 * @return the dialect specific representation of the atomar boolean
	 *  expression
	 */
	public abstract T prepareAtomBoolExpr(AtomBoolExpr expr);

	/**
	 * prepareNotExpr returns the dialect specific representation of a given
	 *  not expression.
	 * 
	 * @param expr the not expression to proceed
	 * 
	 * @return the dialect specific representation of the not expression
	 */
	public abstract T prepareNotExpr(NotExpr expr);

	/**
	 * prepareCompareExpr returns the dialect specific representation of a
	 *  given compare expression.
	 * 
	 * @param expr the compare expression to proceed
	 * 
	 * @return the dialect specific representation of the compare expression
	 */
	public abstract T prepareCompareExpr(CompareExpr expr);

	/**
	 * prepareChainedBoolExpr returns the dialect specific representation
	 *  of a given connected boolean expression set.
	 * 
	 * @param expr the connected boolean expression set to
	 *  proceed
	 * 
	 * @return the dialect specific representation of the connected boolean
	 *  expression set
	 */
	public abstract T prepareChainedBoolExpr(ConnectedBoolExpr expr);

	/**
	 * prepareBoolIfThenElseExpr returns the dialect specific representation of
	 *  a given boolean if-then-else expression.
	 * 
	 * @param expr the boolean if-then-else expression to proceed
	 * 
	 * @return the dialect specific representation of the boolean if-then-else
	 *  expression
	 */
	public abstract T prepareBoolIfThenElseExpr(BoolIfThenElseExpr expr);

	/* expressions
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	public abstract V prepareBoolExprAsExpr(BoolExpression boolExpr);

	/**
	 * prepareAtomarExpr returns the dialect specific representation of a given
	 *  atomar expression.
	 * 
	 * @param expr the atomar expression to proceed
	 * 
	 * @return the dialect specific representation of the atomar expression
	 */
	public abstract V prepareAtomExpr(AtomExpr<?> expr);

	/**
	 * prepareArithmeticExpr returns the dialect specific representation of a
	 *  given arithmetic expression.
	 * 
	 * @param expr the arithmetic expression to proceed
	 * 
	 * @return the dialect specific representation of the arithmetic expression
	 */
	public abstract V prepareArithmeticExpr(ArithmeticExpr expr);

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	public abstract V prepareIfThenElseExpr(IfThenElseExpr expr);

	/* premature expressions
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	public abstract V preparePremAccessibleObjectExpr(PremAccessibleObjectExpr<?> expr);

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	public abstract V preparePremClasscastExpr(PremClasscastExpr expr);

	/* protected methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExpr
	 * 
	 * @return the string representation of the abstract constraint
	 */
	protected T getBackendBoolExpression(BoolExpression boolExpr) {
		if (boolExpr instanceof AtomBoolExpr)
			return this.prepareAtomBoolExpr((AtomBoolExpr) boolExpr);
		else if (boolExpr instanceof NotExpr)
			return this.prepareNotExpr((NotExpr) boolExpr);
		else if (boolExpr instanceof CompareExpr)
			return this.prepareCompareExpr((CompareExpr) boolExpr);
		else if (boolExpr instanceof ConnectedBoolExpr)
			return this.prepareChainedBoolExpr((ConnectedBoolExpr) boolExpr);
		else if (boolExpr instanceof BoolIfThenElseExpr)
			return this.prepareBoolIfThenElseExpr((BoolIfThenElseExpr) boolExpr);
		else {
			String message = "unsupported boolean expression \"" + boolExpr + "\" of type \"" + boolExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(Dialect.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	protected V getBackendExpression(Expression expr) {
		if (expr instanceof AtomExpr)
			return this.prepareAtomExpr((AtomExpr<?>) expr);
		else if (expr instanceof ArithmeticExpr)
			return this.prepareArithmeticExpr((ArithmeticExpr) expr);
		else if (expr instanceof IfThenElseExpr)
			return this.prepareIfThenElseExpr((IfThenElseExpr) expr);
		else if (expr instanceof PremAccessibleObjectExpr<?>)
			return this.preparePremAccessibleObjectExpr((PremAccessibleObjectExpr<?>) expr);
		else if (expr instanceof PremClasscastExpr)
			return this.preparePremClasscastExpr((PremClasscastExpr) expr);
		else if (expr instanceof BoolExpression)
			return this.prepareBoolExprAsExpr((BoolExpression) expr);
		else if (expr.isBoolExpr())
			return this.prepareBoolExprAsExpr(expr.toBoolExpr());
		else {
			String message = "unsupported expression \"" + expr + "\" of type \"" + expr.getClass().getSimpleName() + "\"";
			Logger.getLogger(Dialect.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/** package methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param method
	 * 
	 * @return
	 */
	boolean isIntegerValueMethod(Method method) {
		return CompareUtils.equalsAny(method, preparableIntegerValueMethods);
	}

	/**
	 * COMMENT
	 * 
	 * @param method
	 * 
	 * @return
	 */
	boolean isFloatValueMethod(Method method) {
		return CompareUtils.equalsAny(method, preparableFloatValueMethods);
	}

	/**
	 * COMMENT
	 * 
	 * @param method
	 * 
	 * @return
	 */
	boolean isDoubleValueMethod(Method method) {
		return CompareUtils.equalsAny(method, preparableDoubleValueMethods);
	}

	/**
	 * COMMENT
	 * 
	 * @param expr
	 */
	void clearExtraExprs() {
		this.extraExprs.clear();
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExpr
	 */
	void addExtraExpr(BoolExpression boolExpr) {
		this.extraExprs.add(boolExpr);
	}



	/**
	 * COMMENT
	 * 
	 * @param expr
	 */
	List<BoolExpression> getExtraExprs() {
		return this.extraExprs;
	}
}
