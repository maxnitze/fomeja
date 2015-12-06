package de.agra.fomeja.preprocessing.std;

/* imports */
import java.lang.reflect.Method;

import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
import de.agra.fomeja.preprocessing.misc.CharSeq;
import de.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.agra.fomeja.types.BooleanConnector;
import de.agra.fomeja.types.CompareOperator;
import de.agra.fomeja.utils.ExpressionUtils;
import de.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StringEqualsPreprocessor extends MethodExprPreprocessor {
	/** COMMENT */
	private static final Method equalsString = RefactoringUtils.getMethodForClass(String.class, "equals", Object.class);

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return premMethodExpr.getMethod().equals(equalsString);
	}

	@Override
	public Expression prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		AtomStringExpr stringExpr = this.getStringExprForExpr(premMethodExpr.getExpr(), charSeqMap);
		AtomStringExpr argStringExpr = this.getStringExprForExpr(premMethodExpr.getArgumentExpressions().get(0), charSeqMap);

		return this.prepareStringEqualsExpr(stringExpr, argStringExpr, charSeqMap);
	}

	/**
	 * COMMENT
	 * 
	 * @param stringExpr
	 * @param argStringExpr
	 * @param charSeqMap
	 * 
	 * @return
	 */
	private IfThenElseExpr prepareStringEqualsExpr(AtomStringExpr stringExpr, AtomStringExpr argStringExpr, CharSeqMap charSeqMap) {
		CharSeq stringCharSeq = charSeqMap.getOrCreate(stringExpr);
		CharSeq argStringCharSeq = charSeqMap.getOrCreate(argStringExpr);

		BoolExpression boolExpr = null;
		if (!stringCharSeq.isVariable() && !argStringCharSeq.isVariable()) {
			if (stringCharSeq.maxLength() != argStringCharSeq.maxLength())
				boolExpr = new AtomBoolExpr(false);
			else {
				for (int i=0; boolExpr == null && i<stringCharSeq.maxLength(); i++)
					if (!stringCharSeq.get(i).getValue().equals(argStringCharSeq.get(i).getValue()))
						boolExpr = new AtomBoolExpr(false);

				if (boolExpr == null)
					boolExpr = new AtomBoolExpr(true);
			}
		} else {
			ConnectedBoolExpr boolExprSet = new ConnectedBoolExpr(BooleanConnector.AND);
			for (int i=0; i<stringCharSeq.maxLength() || i<argStringCharSeq.maxLength(); i++) {
				if (i<stringCharSeq.maxLength() && i<argStringCharSeq.maxLength()) {
					ConnectedBoolExpr innerBoolExprSet = new ConnectedBoolExpr(BooleanConnector.OR);
					for (int j=0; j<i; j++) {
						innerBoolExprSet.add(
								new CompareExpr(stringCharSeq.get(j), CompareOperator.LESS, new AtomIntegerExpr(0)));
						innerBoolExprSet.add(
								new CompareExpr(argStringCharSeq.get(j), CompareOperator.LESS, new AtomIntegerExpr(0)));
					}
					innerBoolExprSet.add(new CompareExpr(stringCharSeq.get(i), CompareOperator.EQUAL, argStringCharSeq.get(i)));
	
					boolExprSet.add(innerBoolExprSet);
				}
				else if (i<stringCharSeq.maxLength()) {
					boolExprSet.add(new CompareExpr(stringCharSeq.get(i), CompareOperator.LESS, new AtomIntegerExpr(0)));
					break;
				}
				else /** i<charSeq2.maxLength() */ {
					boolExprSet.add(new CompareExpr(argStringCharSeq.get(i), CompareOperator.LESS, new AtomIntegerExpr(0)));
					break;
				}
			}

			if (stringCharSeq.isVariable() && !argStringCharSeq.isVariable())
				stringCharSeq.addLengthValue(CompareOperator.EQUAL, argStringCharSeq.maxLength());
			else if (!stringCharSeq.isVariable() && argStringCharSeq.isVariable())
				argStringCharSeq.addLengthValue(CompareOperator.EQUAL, stringCharSeq.maxLength());

			boolExpr = boolExprSet;
		}

		return ExpressionUtils.boolExprToExpr(boolExpr);
	}
}
