package de.uni_bremen.agra.fomeja.preprocessing.std;

import java.lang.reflect.Method;

import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomArrayExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeq;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StringToCharArrayPreprocessor extends MethodExprPreprocessor {
	/** COMMENT */
	private static final Method toCharArrayString = RefactoringUtils.getMethodForClass(String.class, "toCharArray");

	@Override
	public boolean matches(PremMethodExpr premMethodExpr) {
		return premMethodExpr.getMethod().equals(toCharArrayString);
	}

	@Override
	public AtomArrayExpr<Character> prepare(PremMethodExpr premMethodExpr, CharSeqMap charSeqMap) {
		CharSeq stringCharSeq = charSeqMap.getOrCreate(this.getStringExprForExpr(premMethodExpr.getExpr(), charSeqMap));

		AtomArrayExpr<Character> stringCharArray = new AtomArrayExpr<Character>(Character.class, stringCharSeq.curLength());
		for (int i=0; i<stringCharArray.length(); i++)
			stringCharArray.set(i, stringCharSeq.get(i));
		return stringCharArray;
	}
}
