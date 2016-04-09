package de.uni_bremen.agra.fomeja.preprocessing.std;

import java.lang.reflect.Method;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StringLengthPreprocessor extends MethodExprPreprocessor {
	/** COMMENT */
	private static final Method lengthString = RefactoringUtils.getMethodForClass(String.class, "length");

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return premMethodExpr.getMethod().equals(lengthString);
	}

	@Override
	public Expression prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		return this.getStringExprForExpr(premMethodExpr.getExpr(), charSeqMap).getLengthExpr();
	}
}
