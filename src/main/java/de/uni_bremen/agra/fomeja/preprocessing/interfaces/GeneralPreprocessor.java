package de.uni_bremen.agra.fomeja.preprocessing.interfaces;

/* imports */
import java.lang.reflect.Method;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.exceptions.PreparationException;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeq;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;
import de.uni_bremen.agra.fomeja.utils.ExpressionUtils;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class GeneralPreprocessor<T extends Expression> {
	/** COMMENT */
	private static final Method charAtString = RefactoringUtils.getMethodForClass(String.class, "charAt", int.class);
	/** COMMENT */
	private static final Method substring1String = RefactoringUtils.getMethodForClass(String.class, "substring", int.class);
	/** COMMENT */
	private static final Method substring2String = RefactoringUtils.getMethodForClass(String.class, "substring", int.class, int.class);

	/**
	 * COMMENT
	 */
	public GeneralPreprocessor() { }
	
	/** abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract boolean matches(T expr);

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	public abstract Expression prepare(T expr, CharSeqMap charSeqMap);

	/** protected expr methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	protected AtomStringExpr getStringExprForExpr(Expression expr, CharSeqMap charSeqMap) {
		if (expr instanceof AtomStringExpr) {
			charSeqMap.getOrCreate((AtomStringExpr) expr);
			return (AtomStringExpr) expr;
		} else if (expr instanceof PremMethodExpr) {
			PremMethodExpr premMethodExpr = (PremMethodExpr) expr;
			if (premMethodExpr.getMethod().equals(substring1String))
				return this.getStringExprFromSubstring(premMethodExpr.getExpr(),
						premMethodExpr.getArgumentExpressions().get(0), charSeqMap);
			else if (premMethodExpr.getMethod().equals(substring2String))
				return this.getStringExprFromSubstring(premMethodExpr.getExpr(),
						premMethodExpr.getArgumentExpressions().get(0), premMethodExpr.getArgumentExpressions().get(1), charSeqMap);
			else {
				String message = "can not get string expression for premature method expression \"" + premMethodExpr + "\" with method \"" + premMethodExpr.getMethod().getName() + "\"";
				Logger.getLogger(GeneralPreprocessor.class).fatal(message);
				throw new PreparationException(message);
			}
		} else {
			String message = "can not get string expression for expression \"" + expr + "\" of type \"" + expr.getClass().getSimpleName() + "\"";
			Logger.getLogger(GeneralPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	protected Expression getCharExprForExpr(Expression expr, CharSeqMap charSeqMap) {
		if (expr instanceof AtomCharacterExpr)
			return (AtomCharacterExpr) expr;
		else if (expr instanceof PremMethodExpr) {
			PremMethodExpr premMethodExpr = (PremMethodExpr) expr;
			if (premMethodExpr.getMethod().equals(charAtString))
				return this.getCharExprFromCharAt(premMethodExpr.getExpr(),
						premMethodExpr.getArgumentExpressions().get(0), charSeqMap);
			else {
				String message = "can not get character expression for premature method expression \"" + premMethodExpr + "\" with method \"" + premMethodExpr.getMethod().getName() + "\"";
				Logger.getLogger(GeneralPreprocessor.class).fatal(message);
				throw new PreparationException(message);
			}
		} else {
			String message = "can not get character expression for expression \"" + expr + "\" of type \"" + expr.getClass().getSimpleName() + "\"";
			Logger.getLogger(GeneralPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param beginIdxExpr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomStringExpr getStringExprFromSubstring(Expression expr, Expression beginIdxExpr, CharSeqMap charSeqMap) {
		return this.getStringExprFromSubstring(expr, beginIdxExpr, null, charSeqMap);
	}

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param beginIdxExpr COMMENT
	 * @param endIdxExpr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private AtomStringExpr getStringExprFromSubstring(Expression expr, Expression beginIdxExpr, Expression endIdxExpr, CharSeqMap charSeqMap) {
		CharSeq exprCharSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(expr, charSeqMap));

		/** get character sequence for substring expression */
		String substringName = exprCharSeq.getName() + "_substring_" + beginIdxExpr + (endIdxExpr != null ? "-" + endIdxExpr : "");
		AtomStringExpr substringExpr = new AtomStringExpr(substringName, null);

		if (ExpressionUtils.isFinishedAtomExpr(beginIdxExpr, AtomIntegerExpr.class)
				&& (endIdxExpr == null || ExpressionUtils.isFinishedAtomExpr(endIdxExpr, AtomIntegerExpr.class))) {
			int beginIdx = ((AtomIntegerExpr) beginIdxExpr).getValue();
			int endIdx = endIdxExpr != null ? ((AtomIntegerExpr) endIdxExpr).getValue() : exprCharSeq.maxLength();

			exprCharSeq.addLengthValue(CompareOperator.GREATER, endIdxExpr != null ? endIdx : beginIdx);

			CharSeq substringCharSeq = charSeqMap.get(substringExpr.getName());
			if (substringCharSeq == null) {
				substringCharSeq = charSeqMap.getOrCreate(substringExpr);

				if (endIdxExpr != null)
					substringCharSeq.addLengthValue(CompareOperator.EQUAL, endIdx-beginIdx);
				else
					substringCharSeq.addLengthValue(CompareOperator.LESS_EQUAL, endIdx-beginIdx);

				charSeqMap.addSubstringExpr(exprCharSeq, substringCharSeq, beginIdx, endIdx);
			}

			return substringCharSeq.getExpr();
		}
		else { // TODO implement
			String message = "can not get substring character sequence for non-finished bound expressions \"" + beginIdxExpr + "\" and \"" + endIdxExpr + "\" (yet)";
			Logger.getLogger(GeneralPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param indexExpr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private Expression getCharExprFromCharAt(Expression expr, Expression indexExpr, CharSeqMap charSeqMap) {
		CharSeq exprCharSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(expr, charSeqMap));

		if (ExpressionUtils.isFinishedAtomExpr(indexExpr, AtomIntegerExpr.class)) {
			charSeqMap.addSubsequentLengthValue(exprCharSeq.getExpr(), CompareOperator.GREATER, (AtomIntegerExpr) indexExpr);
			return exprCharSeq.get(((AtomIntegerExpr) indexExpr).getValue());
		} else {
			IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new AtomCharacterExpr('\0'));
			for (int i=0; i<=exprCharSeq.maxLength(); i++) {
				if (i<=exprCharSeq.minLength())
					ifThenElseExpr.add(new CompareExpr(indexExpr, CompareOperator.EQUAL, new AtomIntegerExpr(i)), exprCharSeq.get(i));
				else
					ifThenElseExpr.add(
							new ConnectedBoolExpr(BooleanConnector.AND,
									new CompareExpr(exprCharSeq.getExpr().getLengthExpr(), CompareOperator.GREATER, new AtomIntegerExpr(i)),
									new CompareExpr(indexExpr, CompareOperator.EQUAL, new AtomIntegerExpr(i))),
							exprCharSeq.get(i));
			}

			return ifThenElseExpr;
		}
	}
}
