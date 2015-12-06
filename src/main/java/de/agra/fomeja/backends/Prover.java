package de.agra.fomeja.backends;

/* imports */
import java.util.List;

import de.agra.fomeja.backends.datatypes.Constraint;
import de.agra.fomeja.backends.datatypes.ResultModel;
import de.agra.fomeja.backends.parameterobjects.ParameterObject;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.exceptions.SatisfyException;

/**
 * Prover is an interface for all possible theorem provers to extend.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class Prover<T extends Dialect<?, ?>> {
	/** the dialect of the prover */
	private final T dialect;

	/**
	 * Constructor for a new prover.
	 * 
	 * @param dialect the dialect of the new prover
	 */
	public Prover(T dialect) {
		this.dialect = dialect;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public T getDialect() {
		return this.dialect;
	}

	/* abstract methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @throws SatisfyException
	 */
	public abstract void resetSolver() throws SatisfyException;

	/**
	 * COMMENT
	 * 
	 * @param boolExprs
	 * 
	 * @return
	 * 
	 * @throws SatisfyException
	 */
	public abstract ResultModel solveNext(List<BoolExpression> boolExprs) throws SatisfyException;

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * solveAndAssign solves the theorem given by the single theorems using the
	 *  prover (needs to be an smt2 prover). Afterwards the solved
	 *  configuration is assigned to the parameter object of the theorem.
	 * 
	 * @param constraint COMMENT
	 * 
	 * @throws SatisfyException if one of the single theorems is not
	 *  satisfiable for the current component
	 */
	public void solveAndAssign(Constraint constraint) throws SatisfyException {
		this.assign(constraint, this.solveNext(constraint.getConstraintExprs()));
	}

	/**
	 * COMMENT
	 * 
	 * @param constraint
	 * @param proverResults
	 */
	public void assign(Constraint constraint, ResultModel proverResults) {
		for (ParameterObject parameterObject : constraint.getParameterObjects())
			if (!parameterObject.isAssigned() && parameterObject.getPreFieldList().last().isVariable())
				parameterObject.assign(proverResults);
	}

	/**
	 * COMMENT
	 */
	public void clearExtraExprs() {
		this.getDialect().clearExtraExprs();
	}

	/**
	 * COMMENT
	 * 
	 * @param boolExpr
	 */
	public void addExtraExpr(BoolExpression boolExpr) {
		this.getDialect().addExtraExpr(boolExpr);
	}



	/**
	 * COMMENT
	 */
	public List<BoolExpression> getExtraExprs() {
		return this.getDialect().getExtraExprs();
	}
}
