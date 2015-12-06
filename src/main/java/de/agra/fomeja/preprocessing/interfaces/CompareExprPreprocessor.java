package de.agra.fomeja.preprocessing.interfaces;

/* imports */
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.agra.fomeja.preprocessing.misc.CharSeqMap;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class CompareExprPreprocessor extends GeneralPreprocessor<CompareExpr> {
	@Override
	public abstract BoolExpression prepare(CompareExpr compareExpr, CharSeqMap charSeqMap);
}
