package de.uni_bremen.agra.fomeja.preprocessing.std;

/* imports */
import java.lang.reflect.Method;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
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
public class StringStartsWithPreprocessor extends MethodExprPreprocessor {
	/** COMMENT */
	private static final Method startsWithString = RefactoringUtils.getMethodForClass(String.class, "startsWith", String.class);

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return premMethodExpr.getMethod().equals(startsWithString);
	}

	@Override
	public Expression prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		AtomStringExpr stringExpr = this.getStringExprForExpr(premMethodExpr.getExpr(), charSeqMap);
		AtomStringExpr argStringExpr = this.getStringExprForExpr(premMethodExpr.getArgumentExpressions().get(0), charSeqMap);

		return this.prepareStringStartsWithExpr(stringExpr, argStringExpr, charSeqMap);
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
	private IfThenElseExpr prepareStringStartsWithExpr(AtomStringExpr stringExpr, AtomStringExpr argStringExpr, CharSeqMap charSeqMap) {
		CharSeq stringCharSeq = charSeqMap.getOrCreate(stringExpr);
		CharSeq argStringCharSeq = charSeqMap.getOrCreate(argStringExpr);

		BoolExpression boolExpr = null;
		if (!stringCharSeq.isVariable() && !argStringCharSeq.isVariable()) {
			if (stringCharSeq.maxLength() < argStringCharSeq.maxLength())
				boolExpr = new AtomBoolExpr(false);
			else {
				for (int i=0; boolExpr == null && i<argStringCharSeq.maxLength(); i++)
					if (!stringCharSeq.get(i).getValue().equals(argStringCharSeq.get(i).getValue()))
						boolExpr = new AtomBoolExpr(false);

				if (boolExpr == null)
					boolExpr = new AtomBoolExpr(true);
			}
		} else if (stringCharSeq.isVariable() && !argStringCharSeq.isVariable()) {
			ConnectedBoolExpr boolExprs = new ConnectedBoolExpr(BooleanConnector.AND);

			for (int i=0; i<argStringCharSeq.maxLength(); i++)
				boolExprs.add(new CompareExpr(stringCharSeq.get(i), CompareOperator.EQUAL, argStringCharSeq.get(i)));
			stringCharSeq.addLengthValue(CompareOperator.GREATER_EQUAL, argStringCharSeq.maxLength());

			boolExpr = boolExprs;
		} else if (!stringCharSeq.isVariable() && argStringCharSeq.isVariable()) {
			ConnectedBoolExpr boolExprs = new ConnectedBoolExpr(BooleanConnector.AND);

			for (int i=0; i<stringCharSeq.maxLength(); i++)
				boolExprs.add(new ConnectedBoolExpr(
						BooleanConnector.OR,
						new CompareExpr(stringCharSeq.get(i), CompareOperator.EQUAL, argStringCharSeq.get(i)),
						new CompareExpr(new AtomIntegerExpr(0), CompareOperator.GREATER, argStringCharSeq.get(i))));
			argStringCharSeq.addLengthValue(CompareOperator.LESS_EQUAL, stringCharSeq.maxLength());

			boolExpr = boolExprs;
		} else { // charSeq1.isVariable && charSeq2.isVariable
			ConnectedBoolExpr boolExprs = new ConnectedBoolExpr(BooleanConnector.AND);

			for (int i=0; i<stringCharSeq.maxLength(); i++)
				boolExprs.add(new ConnectedBoolExpr(
						BooleanConnector.OR,
						new CompareExpr(stringCharSeq.get(i), CompareOperator.EQUAL, argStringCharSeq.get(i)),
						new CompareExpr(new AtomIntegerExpr(0), CompareOperator.GREATER, argStringCharSeq.get(i))));

			boolExpr = boolExprs;
		}

		return ExpressionUtils.boolExprToExpr(boolExpr);
	}
}
