package de.uni_bremen.agra.fomeja.preprocessing.std;

/* imports */
import java.lang.reflect.Method;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
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
public class StringCharAtPreprocessor extends MethodExprPreprocessor {
	/** COMMENT */
	private static final Method charAtString = RefactoringUtils.getMethodForClass(String.class, "charAt", int.class);

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return premMethodExpr.getMethod().equals(charAtString);
	}

	@Override
	public Expression prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		CharSeq charSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(premMethodExpr.getExpr(), charSeqMap));
		Expression indexExpr = (Expression) premMethodExpr.getArgumentExpressions().get(0);

		if (ExpressionUtils.isFinishedAtomExpr(indexExpr, AtomIntegerExpr.class)) {
			charSeqMap.addSubsequentLengthValue(charSeq.getExpr(), CompareOperator.GREATER, (AtomIntegerExpr) indexExpr);
			return charSeq.get(((AtomIntegerExpr) indexExpr).getValue());
		} else {
			IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new AtomCharacterExpr('\0'));
			for (int i=0; i<=charSeq.maxLength(); i++) {
				if (i<=charSeq.minLength())
					ifThenElseExpr.add(new CompareExpr(indexExpr, CompareOperator.EQUAL, new AtomIntegerExpr(i)), charSeq.get(i));
				else
					ifThenElseExpr.add(
							new ConnectedBoolExpr(BooleanConnector.AND,
									new CompareExpr(charSeq.getExpr().getLengthExpr(), CompareOperator.GREATER, new AtomIntegerExpr(i)),
									new CompareExpr(indexExpr, CompareOperator.EQUAL, new AtomIntegerExpr(i))),
							charSeq.get(i));
			}

			return ifThenElseExpr;
		}
	}
}
