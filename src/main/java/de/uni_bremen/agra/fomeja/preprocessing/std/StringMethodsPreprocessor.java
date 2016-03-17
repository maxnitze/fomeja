package de.uni_bremen.agra.fomeja.preprocessing.std;

/* imports */
import java.lang.reflect.Method;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.exceptions.DialectException;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeq;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;
import de.uni_bremen.agra.fomeja.utils.CompareUtils;
import de.uni_bremen.agra.fomeja.utils.ExpressionUtils;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;
import de.uni_bremen.agra.fomeja.utils.StringUtils;
import de.uni_bremen.agra.fomeja.utils.constraintmethods.StringMethods;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StringMethodsPreprocessor extends MethodExprPreprocessor {
	/** COMENT */
	private static final Method isASCIIStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "isASCII", char.class);
	/** COMENT */
	private static final Method allCharsASCIIStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "allCharsASCII", String.class);
	/** COMENT */
	private static final Method anyCharASCIIStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "anyCharASCII", String.class);
	/** COMENT */
	private static final Method isUTF8StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "isUTF8", char.class);
	/** COMENT */
	private static final Method allCharsUTF8StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "allCharsUTF8", String.class);
	/** COMENT */
	private static final Method anyCharUTF8StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "anyCharUTF8", String.class);
	/** COMENT */
	private static final Method isUTF16StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "isUTF16", char.class);
	/** COMENT */
	private static final Method allCharsUTF16StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "allCharsUTF16", String.class);
	/** COMENT */
	private static final Method anyCharUTF16StringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "anyCharUTF16", String.class);

	/** COMENT */
	private static final Method hasCharIntStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasChar", String.class, int.class);
	/** COMENT */
	private static final Method hasCharCharStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasChar", String.class, char.class);
	/** COMENT */
	private static final Method hasAllCharsIntsStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAllChars", String.class, int[].class);
	/** COMENT */
	private static final Method hasAllCharsCharsStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAllChars", String.class, char[].class);
	/** COMENT */
	private static final Method hasAllCharsStringStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAllChars", String.class, String.class);
	/** COMENT */
	private static final Method hasAnyCharIntsStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAnyChar", String.class, int[].class);
	/** COMENT */
	private static final Method hasAnyCharCharsStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAnyChar", String.class, char[].class);
	/** COMENT */
	private static final Method hasAnyCharStringStringMethod = RefactoringUtils.getMethodForClass(StringMethods.class, "hasAnyChar", String.class, String.class);

	/** COMMENT*/
	public static final Method[] preparableStringMethodMethods = new Method[] {
		isASCIIStringMethod, allCharsASCIIStringMethod, anyCharASCIIStringMethod,
		isUTF8StringMethod, allCharsUTF8StringMethod, anyCharUTF8StringMethod,
		isUTF16StringMethod, allCharsUTF16StringMethod, anyCharUTF16StringMethod,

		hasCharIntStringMethod, hasCharCharStringMethod,
		hasAllCharsIntsStringMethod, hasAllCharsCharsStringMethod, hasAllCharsStringStringMethod,
		hasAnyCharIntsStringMethod, hasAnyCharCharsStringMethod, hasAnyCharStringStringMethod
	};

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return CompareUtils.equalsAny(premMethodExpr.getMethod(), preparableStringMethodMethods);
	}

	@Override
	public Expression prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		if (premMethodExpr.getMethod().equals(isASCIIStringMethod)
				|| premMethodExpr.getMethod().equals(allCharsASCIIStringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAllChars(premMethodExpr, StringUtils.MAX_ASCII, charSeqMap));
		else if (premMethodExpr.getMethod().equals(anyCharASCIIStringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAnyChar(premMethodExpr, StringUtils.MAX_ASCII, charSeqMap));
		else if (premMethodExpr.getMethod().equals(isUTF8StringMethod)
				|| premMethodExpr.getMethod().equals(allCharsUTF8StringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAllChars(premMethodExpr, StringUtils.MAX_UTF8, charSeqMap));
		else if (premMethodExpr.getMethod().equals(anyCharUTF8StringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAnyChar(premMethodExpr, StringUtils.MAX_UTF8, charSeqMap));
		else if (premMethodExpr.getMethod().equals(isUTF16StringMethod)
				|| premMethodExpr.getMethod().equals(allCharsUTF16StringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAllChars(premMethodExpr, StringUtils.MAX_UTF16, charSeqMap));
		else if (premMethodExpr.getMethod().equals(anyCharUTF16StringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodAnyChar(premMethodExpr, StringUtils.MAX_UTF16, charSeqMap));
		else if (premMethodExpr.getMethod().equals(hasCharIntStringMethod)
				|| premMethodExpr.getMethod().equals(hasCharCharStringMethod)
				|| premMethodExpr.getMethod().equals(hasAllCharsIntsStringMethod)
				|| premMethodExpr.getMethod().equals(hasAllCharsCharsStringMethod)
				|| premMethodExpr.getMethod().equals(hasAllCharsStringStringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodHasChars(
							premMethodExpr.getArgumentExpressions().get(0), premMethodExpr.getArgumentExpressions().get(1), BooleanConnector.AND, charSeqMap));
		else if (premMethodExpr.getMethod().equals(hasAnyCharIntsStringMethod)
				|| premMethodExpr.getMethod().equals(hasAnyCharCharsStringMethod)
				|| premMethodExpr.getMethod().equals(hasAnyCharStringStringMethod))
			return ExpressionUtils.boolExprToExpr(this.prepareStringMethodHasChars(
							premMethodExpr.getArgumentExpressions().get(0), premMethodExpr.getArgumentExpressions().get(1), BooleanConnector.OR, charSeqMap));
		else {
			String message = "string method \"" + premMethodExpr.getMethod().getName() + "\" is no preparable method from the class \"" + StringMethods.class.getSimpleName() + "\"";
			Logger.getLogger(StringMethodsPreprocessor.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param premMethodExpr COMMENT
	 * @param upperBoundary COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression prepareStringMethodAllChars(PremMethodExpr premMethodExpr, int upperBoundary, CharSeqMap charSeqMap) {
		Expression argExpr = premMethodExpr.getArgumentExpressions().get(0);
		if (ClassUtils.isCharType(argExpr.getResultType()))
			return new CompareExpr(this.getCharExprForExpr(argExpr, charSeqMap), CompareOperator.LESS, new AtomIntegerExpr(upperBoundary));
		else if (String.class.isAssignableFrom(argExpr.getResultType())) {
			CharSeq charSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(argExpr, charSeqMap));

			ConnectedBoolExpr boolExprSet = new ConnectedBoolExpr(BooleanConnector.AND);
			for (int i=0; i<charSeq.maxLength(); i++) {
				ConnectedBoolExpr innerBoolExprSet = new ConnectedBoolExpr(BooleanConnector.OR);
				if (i>=charSeq.minLength())
					for (int j=charSeq.minLength(); j<i; j++)
						innerBoolExprSet.add(new CompareExpr(charSeq.get(j), CompareOperator.LESS, new AtomIntegerExpr(0)));
				innerBoolExprSet.add(new CompareExpr(charSeq.get(i), CompareOperator.LESS, new AtomIntegerExpr(upperBoundary)));
				boolExprSet.add(innerBoolExprSet);
			}

			return boolExprSet;
		} else {
			String message = "can not prepare \"allChars\" for argument expression \"" + argExpr + "\" of type \"" + argExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(StringMethodsPreprocessor.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param premMethodExpr COMMENT
	 * @param upperBoundary COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression prepareStringMethodAnyChar(PremMethodExpr premMethodExpr, int upperBoundary, CharSeqMap charSeqMap) {
		Expression argExpr = premMethodExpr.getArgumentExpressions().get(0);
		if (ClassUtils.isCharType(argExpr.getResultType()))
			return new CompareExpr(this.getCharExprForExpr(argExpr, charSeqMap), CompareOperator.LESS, new AtomIntegerExpr(upperBoundary));
		else if (String.class.isAssignableFrom(argExpr.getResultType())) {
			CharSeq charSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(argExpr, charSeqMap));

			ConnectedBoolExpr boolExprSet = new ConnectedBoolExpr(BooleanConnector.OR);
			for (int i=0; i<charSeq.maxLength(); i++) {
				ConnectedBoolExpr innerBoolExprSet = new ConnectedBoolExpr(BooleanConnector.AND);
				if (i>=charSeq.minLength())
					for (int j=charSeq.minLength(); j<=i; j++)
						innerBoolExprSet.add(new CompareExpr(charSeq.get(j), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(0)));
				innerBoolExprSet.add(new CompareExpr(charSeq.get(i), CompareOperator.LESS, new AtomIntegerExpr(upperBoundary)));
				boolExprSet.add(innerBoolExprSet);
			}

			return boolExprSet;
		} else {
			String message = "can not prepare \"anyChar\" for argument expression \"" + argExpr + "\" of type \"" + argExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(StringMethodsPreprocessor.class).fatal(message);
			throw new DialectException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param stringExpr COMMENT
	 * @param charExpr COMMENT
	 * @param connector COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private ConnectedBoolExpr prepareStringMethodHasChars(Expression stringExpr, Expression charExpr, BooleanConnector connector, CharSeqMap charSeqMap) {
		String message;
		if (stringExpr instanceof AtomStringExpr)
			return this.prepareStringMethodHasChars(charSeqMap.getOrCreate((AtomStringExpr) stringExpr), charExpr, connector, charSeqMap);
		else if (stringExpr.getResultType().equals(String.class))
			throw new DialectException("can not prepare \"hasChar(char)\" on expression \"" + stringExpr + "\" resulting in \"String\" yet");
		else
			message = "can not prepare \"hasChar(char)\" on expression \"" + stringExpr + "\" resulting in \"" + stringExpr.getResultType().getSimpleName() + "\"";

		Logger.getLogger(StringMethodsPreprocessor.class).fatal(message);
		throw new DialectException(message);
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeq COMMENT
	 * @param expr COMMENT
	 * @param connector COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private ConnectedBoolExpr prepareStringMethodHasChars(CharSeq charSeq, Expression expr, BooleanConnector connector, CharSeqMap charSeqMap) {
		String message;
		if (expr instanceof AtomIntegerExpr || expr instanceof AtomCharacterExpr)
			return this.prepareStringMethodHasChars(charSeq, new AtomExpr<?>[] { (AtomExpr<?>) expr }, connector);
		else if (expr instanceof AtomArrayExpr<?>) {
			AtomArrayExpr<?> arrayExpr = (AtomArrayExpr<?>) expr;
			if (ClassUtils.isAssignable(Integer.class, arrayExpr.getType())
					|| ClassUtils.isAssignable(Character.class, arrayExpr.getType())) {
				boolean allAtomar = true;
				AtomExpr<?>[] atomExprs = new AtomExpr<?>[arrayExpr.length()];
				for (int i=0; i<arrayExpr.length(); i++) {
					Expression arrayElement = arrayExpr.get(i);
					if (arrayElement != null && arrayElement instanceof AtomExpr<?>)
						atomExprs[i] = (AtomExpr<?>) arrayElement;
					else {
						allAtomar = false;
						break;
					}
				}

				if (allAtomar)
					return this.prepareStringMethodHasChars(charSeq, atomExprs, connector);
				else
					message = "can not prepare \"hasChars\" method for array expression \"" + arrayExpr + "\" with non-atomar elements";
			} else
				message = "can not prepare \"hasChars\" method for array expression \"" + arrayExpr + "\" of type \"" + arrayExpr.getType().getSimpleName() + "\"";
		} else if (expr.getResultType().equals(String.class)) {
			AtomStringExpr atomStringExpr;
			if (expr instanceof AtomStringExpr)
				atomStringExpr = (AtomStringExpr) expr;
			else
				throw new DialectException("prepare \"hasChars\" for non-atomar string parameter not implemented yet!");

			CharSeq paramCharSeq = charSeqMap.getOrCreate(atomStringExpr);
			AtomArrayExpr<Character> paramCharArrayExpr = new AtomArrayExpr<Character>(Character.class, paramCharSeq.maxLength());
			for (int i=0; i<paramCharSeq.maxLength(); i++)
				paramCharArrayExpr.set(i, paramCharSeq.get(i));
			return this.prepareStringMethodHasChars(charSeq, paramCharArrayExpr, connector, charSeqMap);
		} else
			message = "can not prepare \"hasChars\" method for parameter \"" + expr + "\" resulting in type \"" + expr.getResultType().getSimpleName() + "\"";

		Logger.getLogger(StringMethodsPreprocessor.class).fatal(message);
		throw new DialectException(message);
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeq COMMENT
	 * @param atomExprs COMMENT
	 * @param outerConnector COMMENT
	 * 
	 * @return COMMENT
	 */
	private ConnectedBoolExpr prepareStringMethodHasChars(CharSeq charSeq, AtomExpr<?>[] atomExprs, BooleanConnector outerConnector) {
		ConnectedBoolExpr outerChainedExpr = new ConnectedBoolExpr(outerConnector);
		for (AtomExpr<?> integerExpr : atomExprs) {
			ConnectedBoolExpr chainedExpr = new ConnectedBoolExpr(BooleanConnector.OR);
			for (int i=0; i<charSeq.maxLength(); i++) {
				ConnectedBoolExpr innerChainedExpr = new ConnectedBoolExpr(BooleanConnector.AND);
				for (int j=0; j<i; j++)
					innerChainedExpr.add(new CompareExpr(charSeq.get(j), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(0)));
				innerChainedExpr.add(new CompareExpr(charSeq.get(i), CompareOperator.EQUAL, integerExpr));
				chainedExpr.add(innerChainedExpr);
			}
			outerChainedExpr.add(chainedExpr);
		}
		return outerChainedExpr;
	}
}
