package de.uni_bremen.agra.fomeja.preprocessing.interfaces;

import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public abstract class CompareExprPreprocessor extends GeneralPreprocessor<CompareExpr> {
	@Override
	public abstract BoolExpression prepare(CompareExpr compareExpr, CharSeqMap charSeqMap);
}
