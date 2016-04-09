package de.uni_bremen.agra.fomeja.backends;

/* imports */
import java.util.List;

import org.apache.log4j.Logger;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import de.uni_bremen.agra.fomeja.backends.datatypes.ResultModel;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.exceptions.SatisfyException;

/**
 * 
 * @author Max Nitze
 */
public class Z3SMTIIJava extends Prover<SMTIIJava> {
	/** COMMENT */
	private Solver solver;

	/** COMMENT */
	private boolean hasOneTimeExprs;

	/**
	 * COMMENT
	 */
	public Z3SMTIIJava() {
		super(new SMTIIJava());

		try {
			this.solver = this.getDialect().getContext().mkSolver();
		} catch (Z3Exception e) {
			String message = "could not create solver due to z3 exception: " + e.getMessage();
			Logger.getLogger(Z3SMTIIJava.class).fatal(message);
			throw new IllegalArgumentException(message);
		}

		this.hasOneTimeExprs = false;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public void resetSolver() throws SatisfyException {
		try {
			this.solver.reset();
		} catch (Z3Exception e) {
			throw new SatisfyException("could not reset solver due to z3 exception: " + e.getMessage());
		}
	}

	@Override
	public ResultModel solveNext(List<BoolExpression> boolExprs) throws SatisfyException {
		List<BoolExpression> oneTimeExprs = this.getDialect().getExtraExprs();

		try {
			if (this.hasOneTimeExprs)
				this.solver.pop();

			for (BoolExpr boolExpr : this.getDialect().format(boolExprs))
				this.solver.add(boolExpr);
			this.solver.push();

			for (BoolExpr boolExpr : this.getDialect().format(oneTimeExprs))
				this.solver.add(boolExpr);
			this.hasOneTimeExprs = oneTimeExprs.size() > 0;

			if (this.solver.check() == Status.SATISFIABLE)
				return this.getDialect().parseResult(this.solver.getModel());
			else
				throw new SatisfyException("one or more of the constraints are not satisfiable for the given instance");
		} catch (Z3Exception e) {
			throw new SatisfyException("could not solve and/or assign due to z3 exception: " + e.getMessage());
		}
	}
}
