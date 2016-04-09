package de.uni_bremen.agra.fomeja.preprocessing;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.datatypes.Constraint;
import de.uni_bremen.agra.fomeja.decompiling.expressions.ArithmeticExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.IfThenElseExpr.CondExprPair;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.NotExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolIfThenElseExpr.CondBoolExprPair;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremAccessibleObjectExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArrayelementExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremArraylengthExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremClasscastExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremConstructorExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremFieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremGetfieldExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremLoopStmtExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremMethodExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PremStmtSeqExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.premature.PrematureExpr;
import de.uni_bremen.agra.fomeja.exceptions.PreparationException;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.CompareExprPreprocessor;
import de.uni_bremen.agra.fomeja.preprocessing.interfaces.MethodExprPreprocessor;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeq;
import de.uni_bremen.agra.fomeja.preprocessing.misc.CharSeqMap;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ConstraintPreprocessor {
	/** COMMENT */
	private LinkedList<CompareExprPreprocessor> compareExprPreprocessors;
	/** COMMENT */
	private LinkedList<MethodExprPreprocessor> methodExprPreprocessors;

	/** COMMENT */
	private CharSeqMapPreprocessor charSeqMapPreprocessor;
	/** COMMENT */
	private CharSeqMap charSeqMap;

	/**
	 * COMMENT
	 */
	public ConstraintPreprocessor() {
		this.compareExprPreprocessors = new LinkedList<CompareExprPreprocessor>();
		this.methodExprPreprocessors = new LinkedList<MethodExprPreprocessor>();

		this.charSeqMapPreprocessor = new CharSeqMapPreprocessor();
		this.charSeqMap = new CharSeqMap();
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * 
	 * @return COMMENT
	 */
	public int getMaxLength(String name) {
		return this.charSeqMap.get(name).maxLength();
	}

	/* public class methods
	 * ----- ----- ----- ----- ----- */
	/**
	 * COMMENT
	 * 
	 * @param constraint COMMENT
	 * 
	 * @return COMMENT
	 */
	public BoolExpression prepare(Constraint constraint) {
		return this.prepare(constraint.getConstraintExprs());
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExprs COMMENT
	 * 
	 * @return COMMENT
	 */
	public BoolExpression prepare(List<BoolExpression> boolExprs) {
		CharSeqMap charSeqMap = this.getCurrentCharSeqMap(boolExprs);

		ConnectedBoolExpr preparedBoolExprs = new ConnectedBoolExpr(BooleanConnector.AND);
		for (BoolExpression boolExpr : boolExprs)
			preparedBoolExprs.add(this.prepare(boolExpr, charSeqMap));
		this.charSeqMap.merge(charSeqMap);

		return new ConnectedBoolExpr(BooleanConnector.AND, charSeqMap.getCharSeqExprs(), preparedBoolExprs.simplify());
	}


	/**
	 * COMMENT
	 * 
	 * @param compareExprPreprocessor COMMENT
	 */
	public void register(CompareExprPreprocessor compareExprPreprocessor) {
		this.compareExprPreprocessors.addFirst(compareExprPreprocessor);
	}

	/**
	 * COMMENT
	 * 
	 * @param methodExprPreprocessor COMMENT
	 */
	public void register(MethodExprPreprocessor methodExprPreprocessor) {
		this.methodExprPreprocessors.addFirst(methodExprPreprocessor);
	}

	/* private matches methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	private boolean matches(BoolExpression boolExpr) {
		if (boolExpr instanceof AtomBoolExpr)
			return false;
		else if (boolExpr instanceof NotExpr)
			return this.matches(((NotExpr) boolExpr).getBoolExpr());
		else if (boolExpr instanceof CompareExpr) {
			CompareExpr compareExpr = (CompareExpr) boolExpr;
			for (CompareExprPreprocessor compareExprPreprocessor : this.compareExprPreprocessors)
				if (compareExprPreprocessor.matches(compareExpr))
					return true;

			return this.matches(compareExpr.getExpr1()) || this.matches(compareExpr.getExpr2());
		} else if (boolExpr instanceof ConnectedBoolExpr) {
			for (BoolExpression innerBoolExpr : ((ConnectedBoolExpr) boolExpr).getBoolExprs())
				if (this.matches(innerBoolExpr))
					return true;
			return false;
		} else if (boolExpr instanceof BoolIfThenElseExpr) {
			for (CondBoolExprPair condBoolExprPair : ((BoolIfThenElseExpr) boolExpr).getCondBoolExprPairs())
				if (this.matches(condBoolExprPair.getCondition()) || this.matches(condBoolExprPair.getBoolExpr()))
					return true;
			return this.matches(((BoolIfThenElseExpr) boolExpr).getElseCaseExpr());
		} else {
			String message = "can not match bool expression \"" + boolExpr + "\" of unknown type \"" + boolExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 *
	 * @return COMMENT
	 */
	private boolean matches(Expression expr) {
		if (expr instanceof BoolExpression)
			return this.matches((BoolExpression) expr);
		else if (expr instanceof AtomExpr<?>)
			return false;
		else if (expr instanceof ArithmeticExpr)
			return this.matches(((ArithmeticExpr) expr).getExpr1()) || this.matches(((ArithmeticExpr) expr).getExpr2());
		else if (expr instanceof IfThenElseExpr) {
			IfThenElseExpr ifThenElseExpr = (IfThenElseExpr) expr;
			for (CondExprPair condExprPair : ifThenElseExpr.getCondExprPairs())
				if (this.matches(condExprPair.getCondition()) || this.matches(condExprPair.getExpr()))
					return true;
			return this.matches(ifThenElseExpr.getElseCaseExpr());
		} else if (expr instanceof PrematureExpr)
			return this.matches((PrematureExpr) expr);
		else {
			String message = "can not match expression \"" + expr + "\" of unknown type \"" + expr.getClass().getSimpleName() + "\"";
			Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param premExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	private boolean matches(PrematureExpr premExpr) {
		if (premExpr instanceof PremMethodExpr) {
			PremMethodExpr premMethodExpr = (PremMethodExpr) premExpr;
			for (MethodExprPreprocessor methodExprPreprocessor : this.methodExprPreprocessors)
				if (methodExprPreprocessor.matches(premMethodExpr))
					return true;

			for (Expression argExpr : premMethodExpr.getArgumentExpressions())
				if (this.matches(argExpr))
					return true;
			return this.matches(premMethodExpr.getExpr());
		} else if (premExpr instanceof PremAccessibleObjectExpr<?>) {
			PremAccessibleObjectExpr<?> premAccessibleObjectExpr = (PremAccessibleObjectExpr<?>) premExpr;
			for (Expression argExpr : premAccessibleObjectExpr.getArgumentExpressions())
				if (this.matches(argExpr))
					return true;
			return this.matches(premAccessibleObjectExpr.getExpr());
		} else if (premExpr instanceof PremArrayelementExpr)
			return this.matches(((PremArrayelementExpr) premExpr).getArrayExpr()) || this.matches(((PremArrayelementExpr) premExpr).getIndexExpr());
		else if (premExpr instanceof PremArraylengthExpr)
			return this.matches(((PremArraylengthExpr) premExpr).getArrayExpr());
		else if (premExpr instanceof PremClasscastExpr)
			return this.matches(((PremClasscastExpr) premExpr).getExpr());
		else if (premExpr instanceof PremGetfieldExpr)
			return this.matches(((PremGetfieldExpr) premExpr).getExpr());
		else if (premExpr instanceof PremLoopStmtExpr)
			return this.matches(((PremLoopStmtExpr) premExpr).getSubstitutedCondition());
		else if (premExpr instanceof PremStmtSeqExpr)
			return false;
		else {
			String message = "can not match premature expression \"" + premExpr + "\" of unknown type \"" + premExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/* private prepare methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExpr COMMENT
	 * @param charSeqMap COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression prepare(BoolExpression boolExpr, CharSeqMap charSeqMap) {
		if (this.matches(boolExpr)) {
			if (boolExpr instanceof AtomBoolExpr)
				return boolExpr;
			else if (boolExpr instanceof NotExpr)
				return new NotExpr(this.prepare(((NotExpr) boolExpr).getBoolExpr(), charSeqMap));
			else if (boolExpr instanceof CompareExpr) {
				CompareExpr compareExpr = (CompareExpr) boolExpr;

				for (CompareExprPreprocessor compareExprPreprocessor : this.compareExprPreprocessors)
					if (compareExprPreprocessor.matches(compareExpr))
						return this.prepare(compareExprPreprocessor.prepare(compareExpr, charSeqMap), charSeqMap);

				return new CompareExpr(this.prepare(compareExpr.getExpr1(), charSeqMap), compareExpr.getOperator(), this.prepare(compareExpr.getExpr2(), charSeqMap));
			} else if (boolExpr instanceof ConnectedBoolExpr) {
				ConnectedBoolExpr chainedBoolExpr = (ConnectedBoolExpr) boolExpr;

				CharSeqMap newCharSeqMap = null;
				ConnectedBoolExpr newChainedBoolExpr = new ConnectedBoolExpr(chainedBoolExpr.getConnector());
				for (BoolExpression innerBoolExpr : chainedBoolExpr.getBoolExprs()) {
					if (chainedBoolExpr.getConnector() == BooleanConnector.OR) {
						CharSeqMap lastNewCharSeqMap = newCharSeqMap;
						newCharSeqMap = new CharSeqMap(charSeqMap);
						if (lastNewCharSeqMap != null)
							newCharSeqMap.addAllSubsequentCharSeqs(lastNewCharSeqMap);

						newChainedBoolExpr.add(this.connectCharSeqMap(newCharSeqMap, this.prepare(innerBoolExpr, newCharSeqMap)));
					} else
						newChainedBoolExpr.add(this.prepare(innerBoolExpr, charSeqMap));
				}

				return newChainedBoolExpr;
			} else if (boolExpr instanceof BoolIfThenElseExpr) {
				BoolIfThenElseExpr boolIfThenElseExpr = (BoolIfThenElseExpr) boolExpr;

				BoolIfThenElseExpr newBoolIfThenElseExpr = new BoolIfThenElseExpr(this.prepare(boolIfThenElseExpr.getElseCaseExpr(), charSeqMap));
				for (CondBoolExprPair condBoolExprPair : boolIfThenElseExpr.getCondBoolExprPairs())
					newBoolIfThenElseExpr.add(this.prepare(condBoolExprPair.getCondition(), charSeqMap), this.prepare(condBoolExprPair.getBoolExpr(), charSeqMap));

				return newBoolIfThenElseExpr;
			} else {
				String message = "can not prepare bool expression \"" + boolExpr + "\" of unknown type \"" + boolExpr.getClass().getSimpleName() + "\"";
				Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
				throw new PreparationException(message);
			}
		} else
			return boolExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @param expr COMMENT
	 * @param charSeqMap COMMENT
	 *
	 * @return COMMENT
	 */
	private Expression prepare(Expression expr, CharSeqMap charSeqMap) {
		if (this.matches(expr)) {
			if (expr instanceof BoolExpression)
				return this.prepare((BoolExpression) expr, charSeqMap);
			else if (expr instanceof AtomExpr<?>) {
				String message = "can not prepare atomar expression \"" + expr + "\"";
				Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
				throw new PreparationException(message);
			} else if (expr instanceof ArithmeticExpr) {
				ArithmeticExpr arithmeticExpr = (ArithmeticExpr) expr;
				return new ArithmeticExpr(this.prepare(arithmeticExpr.getExpr1(), charSeqMap), arithmeticExpr.getOperator(), this.prepare(arithmeticExpr.getExpr2(), charSeqMap));
			} else if (expr instanceof IfThenElseExpr) {
				IfThenElseExpr ifThenElseExpr = (IfThenElseExpr) expr;

				IfThenElseExpr newIfThenElseExpr = new IfThenElseExpr(this.prepare(ifThenElseExpr.getElseCaseExpr(), charSeqMap));
				for (CondExprPair condExprPair : ifThenElseExpr.getCondExprPairs())
					newIfThenElseExpr.add(this.prepare(condExprPair.getCondition(), charSeqMap), this.prepare(condExprPair.getExpr(), charSeqMap));
				return newIfThenElseExpr;
			} else if (expr instanceof PrematureExpr)
				return this.prepare((PrematureExpr) expr, charSeqMap);
			else {
				String message = "can not prepare expression \"" + expr + "\" of unknown type \"" + expr.getClass().getSimpleName() + "\"";
				Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
				throw new PreparationException(message);
			}
		} else
			return expr;
	}

	/**
	 * COMMENT
	 * 
	 * @param premExpr COMMENT
	 * @param charSeqMap COMMENT
	 *
	 * @return COMMENT
	 */
	private Expression prepare(PrematureExpr premExpr, CharSeqMap charSeqMap) {
		if (premExpr instanceof PremMethodExpr) {
			PremMethodExpr premMethodExpr = (PremMethodExpr) premExpr;
			for (MethodExprPreprocessor methodExprPreprocessor : this.methodExprPreprocessors)
				if (methodExprPreprocessor.matches(premMethodExpr))
					return this.prepare(methodExprPreprocessor.prepare(premMethodExpr, charSeqMap), charSeqMap);

			List<Expression> argExprs = new ArrayList<Expression>();
			for (Expression argExpr : premMethodExpr.getArgumentExpressions())
				argExprs.add(this.prepare(argExpr, charSeqMap));
			return new PremMethodExpr(this.prepare(premMethodExpr.getExpr(), charSeqMap), premMethodExpr.getMethod(), argExprs);
		} else if (premExpr instanceof PremConstructorExpr) {
			PremConstructorExpr premConstrExpr = (PremConstructorExpr) premExpr;
			List<Expression> argExprs = new ArrayList<Expression>();
			for (Expression argExpr : premConstrExpr.getArgumentExpressions())
				argExprs.add(this.prepare(argExpr, charSeqMap));
			return new PremConstructorExpr(this.prepare(premConstrExpr.getExpr(), charSeqMap), premConstrExpr.getConstructor(), argExprs);
		} else if (premExpr instanceof PremFieldExpr)
			return new PremFieldExpr(this.prepare(((PremFieldExpr) premExpr).getExpr(), charSeqMap), ((PremFieldExpr) premExpr).getField());
		else if (premExpr instanceof PremArrayelementExpr)
			return new PremArrayelementExpr(
					this.prepare(((PremArrayelementExpr) premExpr).getArrayExpr(), charSeqMap),
					this.prepare(((PremArrayelementExpr) premExpr).getIndexExpr(), charSeqMap));
		else if (premExpr instanceof PremArraylengthExpr)
			return new PremArraylengthExpr(
					this.prepare(((PremArraylengthExpr) premExpr).getArrayExpr(), charSeqMap));
		else if (premExpr instanceof PremClasscastExpr)
			return new PremClasscastExpr(this.prepare(((PremClasscastExpr) premExpr).getExpr(), charSeqMap), ((PremClasscastExpr) premExpr).getKeyword());
		else if (premExpr instanceof PremGetfieldExpr)
			return new PremGetfieldExpr(this.prepare(((PremGetfieldExpr) premExpr).getExpr(), charSeqMap), ((PremGetfieldExpr) premExpr).getField());
		else if (premExpr instanceof PremLoopStmtExpr) {
			PremLoopStmtExpr premLoopStmtExpr = (PremLoopStmtExpr) premExpr;
			CharSeqSet charSeqSet = new CharSeqSet(premLoopStmtExpr.getSubstitutedCondition().getAtomStringExprs(), charSeqMap);

			/** COMMENT ; else case expression is not important, since one of the conditional expressions needs to be true, because all
			 * possible lengths of the strings in the condition are given */
			IfThenElseExpr ifThenElseExpr = new IfThenElseExpr(new AtomIntegerExpr(0));
			while (charSeqSet.increment()) {
				PremLoopStmtExpr clonedPremLoopStmtExpr = premLoopStmtExpr.clone();
				for (Map.Entry<String, Expression> stateExprsEntry : clonedPremLoopStmtExpr.getStateExprs().entrySet())
					clonedPremLoopStmtExpr.putStateExpr(stateExprsEntry.getKey(), this.prepare(stateExprsEntry.getValue().clone(), charSeqMap));

				ifThenElseExpr.add(charSeqSet.getLenghtExpr(), this.prepare(clonedPremLoopStmtExpr.evaluate(), charSeqMap));
			}

			return ifThenElseExpr;
		} else if (premExpr instanceof PremStmtSeqExpr) {
			String message = "can not prepare premature statement sequence expression \"" + premExpr + "\"";
			Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		} else {
			String message = "can not prepare premature expression \"" + premExpr + "\" of unknown type \"" + premExpr.getClass().getSimpleName() + "\"";
			Logger.getLogger(ConstraintPreprocessor.class).fatal(message);
			throw new PreparationException(message);
		}
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param boolExprs COMMENT
	 * 
	 * @return COMMENT
	 */
	private CharSeqMap getCurrentCharSeqMap(List<BoolExpression> boolExprs) {
		return this.charSeqMapPreprocessor.prepare(boolExprs);
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeqMap COMMENT
	 * @param boolExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	private BoolExpression connectCharSeqMap(CharSeqMap charSeqMap, BoolExpression boolExpr) {
		ConnectedBoolExpr charSeqMapLengthExpr = charSeqMap.getCharSeqExprs();
		if (charSeqMapLengthExpr.isEmpty())
			return boolExpr;
		else
			return new ConnectedBoolExpr(BooleanConnector.AND, charSeqMapLengthExpr, boolExpr);
	}

	/* inner classes
	 * ----- ----- ----- ----- ----- */

	private static class CharSeqSet {
		/** COMMENT */
		private int size;
		/** COMMENT */
		private CharSeq[] charSeqs;
		/** COMMENT */
		private boolean isInitialized;

		/**
		 * COMMENT
		 * 
		 * @param atomStringExprs COMMENT
		 * @param charSeqMap COMMENT
		 */
		public CharSeqSet(Set<AtomStringExpr> atomStringExprs, CharSeqMap charSeqMap) {
			this.size = atomStringExprs.size();
			this.charSeqs = new CharSeq[this.size];
			int i=0;
			for (AtomStringExpr atomStringExpr : atomStringExprs)
				this.charSeqs[i++] = charSeqMap.getOrCreate(atomStringExpr);
			this.isInitialized = false;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public boolean increment() {
			if (!this.isInitialized) {
				for (int i=0; i<this.size; i++)
					this.charSeqs[i].setCurLength(this.charSeqs[i].minLength());
				this.isInitialized = true;
				return true;
			} else
				return this.increment(0);
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public ConnectedBoolExpr getLenghtExpr() {
			ConnectedBoolExpr lengthExpr = new ConnectedBoolExpr(BooleanConnector.AND);
			for (int i=0; i<this.size; i++)
				lengthExpr.add(new CompareExpr(this.charSeqs[i].getExpr().getLengthExpr(), CompareOperator.EQUAL, new AtomIntegerExpr(this.charSeqs[i].curLength())));
			return lengthExpr;
		}

		/* overridden object methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public String toString() {
			StringBuilder stringBuilder = new StringBuilder("CharSeqSet:");
			for (int i=0; i<this.size; i++)
				stringBuilder
						.append("\n  ")
						.append(this.charSeqs[i].getName())
						.append(" with length boundaries ")
						.append(this.charSeqs[i].minLength())
						.append(" -- ")
						.append(this.charSeqs[i].maxLength())
						.append(" and with current length ")
						.append(this.charSeqs[i].curLength());
			return stringBuilder.toString();
		}

		/* private methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @param i COMMENT
		 * 
		 * @return COMMENT
		 */
		private boolean increment(int i) {
			if (i < this.size) {
				if (this.charSeqs[i].curLength() < this.charSeqs[i].maxLength()) {
					this.charSeqs[i].setCurLength(this.charSeqs[i].curLength()+1);
					return true;
				} else {
					this.charSeqs[i].setCurLength(this.charSeqs[i].minLength());
					return this.increment(i+1);
				}
			} else
				return false;
		}
	}
}
