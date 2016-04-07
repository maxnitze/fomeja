package de.uni_bremen.agra.fomeja;

/* imports */
import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.Prover;
import de.uni_bremen.agra.fomeja.exceptions.SatisfyException;
import de.uni_bremen.agra.fomeja.utils.FomejaUtils;
import de.uni_bremen.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 *
 * @version 0.9.5
 * @author Max Nitze
 */
public class FomejaSolver {
	/** COMMENT */
	private Prover<?> prover;

	/**
	 * COMMENT
	 */
	public FomejaSolver() {
		this(FomejaDefaults.getDefaultProver());
	}

	/**
	 * COMMENT
	 * 
	 * @param prover COMMENT
	 */
	public FomejaSolver(Prover<?> prover) {
		this.prover = prover;
	}

	/**
	 * validate validates a given component by checking its constraints with a
	 *  given configuration.
	 *
	 * @param component the component to validate
	 *
	 * @return {@code true} if the given configuration matches the constraints
	 *  of the components class, {@code false} otherwise
	 */
	public boolean validate(Object component) {
		return FomejaUtils.validate(component);
	}

	/**
	 * satisfy tries to satisfy the given component by calculating a
	 *  configuration for its variables that satisfies its constraints.
	 *
	 * @param component the component to satisfy
	 *
	 * @return {@code true} if the calculated configuration matches the
	 *  constraints of the components class, {@code false} otherwise
	 */
	public boolean satisfy(Object component) {
		if (RefactoringUtils.hasVariableFields(component.getClass())) {
			try {
				this.prover.solveAndAssign(FomejaUtils.getConstraintForComponent(component));
				return true;
			} catch (SatisfyException e) {
				String message = "failed to satisfy given theorems due to:\n" + e.getMessage();
				Logger.getLogger(FomejaSolver.class).info(message);
				return false;
			}
		} else {
			String message = "the component has no variable fields to satisfy";
			Logger.getLogger(FomejaSolver.class).info(message);
			throw new RuntimeException(message); // TODO change exception type
		}
	}
}
