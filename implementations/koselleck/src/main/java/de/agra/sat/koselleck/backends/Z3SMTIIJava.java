package de.agra.sat.koselleck.backends;

/** imports */
import java.util.List;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.Theorem;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;

/**
 * 
 * @author Max Nitze
 */
public class Z3SMTIIJava extends Prover<SMTIIJava> {
	/**  */
	private Context context;
	/**
	 * 
	 */
	public Z3SMTIIJava() {
		super(new SMTIIJava());

		this.context = this.dialect.getContext();
	}

	@Override
	public void solveAndAssign(Object component, List<AbstractSingleTheorem> singleTheorems) throws NotSatisfiableException {
		Theorem theorem = this.dialect.getConstraintForArguments(component, singleTheorems);

		BoolExpr booleanExpression = this.dialect.format(theorem);

		Solver solver;
		try {
			solver = this.context.MkSolver();
			solver.Assert(booleanExpression);

			Status status = solver.Check();

			if (status != Status.SATISFIABLE)
				throw new NotSatisfiableException("one or more of the constraints are not satisfyable for the given instance");
			else
				this.assign(theorem, this.dialect.parseResult(solver.Model()));
		} catch (Z3Exception e) {
			throw new NotSatisfiableException("could not solve and/or assign due to z3 exception: " + e.getMessage());
		}
	}
}
