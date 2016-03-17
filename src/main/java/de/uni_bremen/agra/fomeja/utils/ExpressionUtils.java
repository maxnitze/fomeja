package de.uni_bremen.agra.fomeja.utils;

/* imports */
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.Prover;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomBooleanExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomDoubleExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomEnumExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomFloatExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.exceptions.EvaluationException;
import de.uni_bremen.agra.fomeja.exceptions.ExpressionException;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 * @version 1.0.0
 */
public final class ExpressionUtils {
	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private ExpressionUtils() {}

	/**
	 * COMMENT
	 * 
	 * @param expr1 the first expression
	 * @param operator the compare operator
	 * @param expr2 the second expression
	 * 
	 * @return
	 */
	public static BoolExpression compareExpressions(Expression expr1, CompareOperator operator, Expression expr2) {
		if (expr1 instanceof AtomExpr<?>
				&& ((AtomExpr<?>) expr1).isFinishedNumberType()
				&& expr2 instanceof AtomExpr<?>
				&& ((AtomExpr<?>) expr2).isFinishedNumberType())
			return ExpressionUtils.evaluateNumberTypes(
						(AtomExpr<?>) expr1, operator, (AtomExpr<?>) expr2);
		else if (expr1 instanceof AtomExpr<?> && expr2 instanceof AtomExpr<?>
				&& ((AtomExpr<?>) expr1).isFinishedType() && ((AtomExpr<?>) expr2).isFinishedType()) {
			switch (operator) {
			case EQUAL:
				return new AtomBoolExpr(((AtomExpr<?>) expr1).equals((AtomExpr<?>) expr2));
			case NOT_EQUAL:
				return new AtomBoolExpr(!((AtomExpr<?>) expr1).equals((AtomExpr<?>) expr2));
			default:
				String message = "could not compare two not numeric types \"" + expr1 + "\" and \"" + expr2 + "\" with operator \"" + operator + "\"";
				Logger.getLogger(ExpressionUtils.class).fatal(message);
				throw new ExpressionException(message);
			}
		} else
			return new CompareExpr(expr1, operator, expr2);
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1 the first atomar expression
	 * @param operator the operator of the single constraint
	 * @param atomExpr2 the second atomar expression
	 * 
	 * @return the atomar boolean expression of the given comparable values
	 *  considering the operator
	 */
	public static AtomBoolExpr evaluateNumberTypes(AtomExpr<?> atomExpr1, CompareOperator operator, AtomExpr<?> atomExpr2) {
		switch(operator) {
		case EQUAL:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) == 0);
		case GREATER:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) > 0);
		case GREATER_EQUAL:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) >= 0);
		case LESS:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) < 0);
		case LESS_EQUAL:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) <= 0);
		case NOT_EQUAL:
			return new AtomBoolExpr(atomExpr1.compareTo(atomExpr2) != 0);
		default:
			String message = "compare operator \"" + operator.getAsciiName() + "\" is not known";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new EvaluationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param object
	 * 
	 * @return
	 */
	public static AtomExpr<?> getAtomExprFromObject(Object object) {
		if (ClassUtils.isBooleanType(object.getClass()))
			return new AtomIntegerExpr((Boolean) object ? 1 : 0);
		else if (ClassUtils.isDoubleType(object.getClass()))
			return new AtomDoubleExpr((Double) object);
		else if (ClassUtils.isFloatType(object.getClass()))
			return new AtomFloatExpr((Float) object);
		else if (ClassUtils.isIntegerType(object.getClass()))
			return new AtomIntegerExpr((Integer) object);
		else if (object.getClass().equals(String.class))
			return new AtomStringExpr((String) object);
		else if (object.getClass().isEnum())
			return new AtomEnumExpr((Enum<?>) object);
		else
			return new AtomObjectExpr(object);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param compareOperator
	 * @param value
	 * 
	 * @return
	 */
	public static CompareExpr getCompareExpr(String name, CompareOperator compareOperator, Object value) {
		if (value instanceof Integer)
			return new CompareExpr(new AtomIntegerExpr(name), compareOperator, new AtomIntegerExpr((Integer) value));
		else if (value instanceof Float)
			return new CompareExpr(new AtomFloatExpr(name), compareOperator, new AtomFloatExpr((Float) value));
		else if (value instanceof Double)
			return new CompareExpr(new AtomDoubleExpr(name), compareOperator, new AtomDoubleExpr((Double) value));
		else if (value instanceof Boolean)
			return new CompareExpr(new AtomBooleanExpr(name), compareOperator, new AtomBooleanExpr((Boolean) value));
		else {
			String message = "can not create compare expression from object type \"" + value.getClass().getSimpleName() + "\"";
			Logger.getLogger(Prover.class).error(message);
			throw new IllegalArgumentException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1
	 * @param atomExpr2
	 * 
	 * @return
	 */
	public static int compareFinishedAtomExprs(AtomExpr<?> atomExpr1, AtomExpr<?> atomExpr2) {
		if (!atomExpr1.isFinishedNumberType() || !atomExpr2.isFinishedNumberType()) {
			String message = "unfinished expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
		else if (atomExpr1 instanceof AtomCharacterExpr)
			return compareFinishedAtomExprs((AtomCharacterExpr) atomExpr1, atomExpr2);
		else if (atomExpr1 instanceof AtomDoubleExpr)
			return compareFinishedAtomExprs((AtomDoubleExpr) atomExpr1, atomExpr2);
		else if (atomExpr1 instanceof AtomFloatExpr)
			return compareFinishedAtomExprs((AtomFloatExpr) atomExpr1, atomExpr2);
		else if (atomExpr1 instanceof AtomIntegerExpr)
			return compareFinishedAtomExprs((AtomIntegerExpr) atomExpr1, atomExpr2);
		else {
			String message = "expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1
	 * @param atomExpr2
	 * 
	 * @return
	 */
	public static int compareFinishedAtomExprs(AtomCharacterExpr atomExpr1, AtomExpr<?> atomExpr2) {
		if (!atomExpr1.isFinishedNumberType() || !atomExpr2.isFinishedNumberType()) {
			String message = "unfinished expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
		else if (atomExpr2 instanceof AtomCharacterExpr)
			return atomExpr1.getValue().compareTo(((AtomCharacterExpr) atomExpr2).getValue());
		else if (atomExpr2 instanceof AtomDoubleExpr)
			return -((AtomDoubleExpr) atomExpr2).getValue().compareTo(new Integer(atomExpr1.getValue()).doubleValue());
		else if (atomExpr2 instanceof AtomFloatExpr)
			return -((AtomFloatExpr) atomExpr2).getValue().compareTo(new Integer(atomExpr1.getValue()).floatValue());
		else if (atomExpr2 instanceof AtomIntegerExpr)
			return -((AtomIntegerExpr) atomExpr2).getValue().compareTo(new Integer(atomExpr1.getValue()));
		else {
			String message = "expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1
	 * @param atomExpr2
	 * 
	 * @return
	 */
	public static int compareFinishedAtomExprs(AtomDoubleExpr atomExpr1, AtomExpr<?> atomExpr2) {
		if (!atomExpr1.isFinishedNumberType() || !atomExpr2.isFinishedNumberType()) {
			String message = "unfinished expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
		else if (atomExpr2 instanceof AtomCharacterExpr)
			return atomExpr1.getValue().compareTo(new Integer(((AtomCharacterExpr) atomExpr2).getValue()).doubleValue());
		else if (atomExpr2 instanceof AtomDoubleExpr)
			return atomExpr1.getValue().compareTo(((AtomDoubleExpr) atomExpr2).getValue());
		else if (atomExpr2 instanceof AtomFloatExpr)
			return atomExpr1.getValue().compareTo(((AtomFloatExpr) atomExpr2).getValue().doubleValue());
		else if (atomExpr2 instanceof AtomIntegerExpr)
			return atomExpr1.getValue().compareTo(((AtomIntegerExpr) atomExpr2).getValue().doubleValue());
		else {
			String message = "expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1
	 * @param atomExpr2
	 * 
	 * @return
	 */
	public static int compareFinishedAtomExprs(AtomFloatExpr atomExpr1, AtomExpr<?> atomExpr2) {
		if (!atomExpr1.isFinishedNumberType() || !atomExpr2.isFinishedNumberType()) {
			String message = "unfinished expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
		else if (atomExpr2 instanceof AtomCharacterExpr)
			return atomExpr1.getValue().compareTo(new Integer(((AtomCharacterExpr) atomExpr2).getValue()).floatValue());
		else if (atomExpr2 instanceof AtomDoubleExpr)
			return -((AtomDoubleExpr) atomExpr2).getValue().compareTo(atomExpr1.getValue().doubleValue());
		else if (atomExpr2 instanceof AtomFloatExpr)
			return atomExpr1.getValue().compareTo(((AtomFloatExpr) atomExpr2).getValue());
		else if (atomExpr2 instanceof AtomIntegerExpr)
			return atomExpr1.getValue().compareTo(((AtomIntegerExpr) atomExpr2).getValue().floatValue());
		else {
			String message = "expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param atomExpr1
	 * @param atomExpr2
	 * 
	 * @return
	 */
	public static int compareFinishedAtomExprs(AtomIntegerExpr atomExpr1, AtomExpr<?> atomExpr2) {
		if (!atomExpr1.isFinishedNumberType() || !atomExpr2.isFinishedNumberType()) {
			String message = "unfinished expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
		else if (atomExpr2 instanceof AtomCharacterExpr)
			return atomExpr1.getValue().compareTo(new Integer(((AtomCharacterExpr) atomExpr2).getValue()));
		else if (atomExpr2 instanceof AtomDoubleExpr)
			return -((AtomDoubleExpr) atomExpr2).getValue().compareTo(atomExpr1.getValue().doubleValue());
		else if (atomExpr2 instanceof AtomFloatExpr)
			return -((AtomFloatExpr) atomExpr2).getValue().compareTo(atomExpr1.getValue().floatValue());
		else if (atomExpr2 instanceof AtomIntegerExpr)
			return atomExpr1.getValue().compareTo(((AtomIntegerExpr) atomExpr2).getValue());
		else {
			String message = "expressions \"" + atomExpr1 + "\" and \"" + atomExpr2 + "\" are not comparable";
			Logger.getLogger(ExpressionUtils.class).fatal(message);
			throw new ExpressionException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExpr
	 * 
	 * @return
	 */
	public static IfThenElseExpr boolExprToExpr(BoolExpression boolExpr) {
		return new IfThenElseExpr(boolExpr, new AtomIntegerExpr(1), new AtomIntegerExpr(0));
	}

	/**
	 * COMMENT
	 * 
	 * @param expr
	 * 
	 * @return
	 */
	public static CompareExpr exprToBoolExpr(Expression expr) {
		return new CompareExpr(expr, CompareOperator.EQUAL, new AtomIntegerExpr(1));
	}



	/**
	 * COMMENT
	 * 
	 * @param expr
	 * @param atomExprClass
	 * 
	 * @return
	 */
	public static boolean isFinishedAtomExpr(Expression expr, Class<? extends AtomExpr<?>> atomExprClass) {
		return atomExprClass.isInstance(expr) && ((AtomExpr<?>) expr).isFinishedType();
	}
}
