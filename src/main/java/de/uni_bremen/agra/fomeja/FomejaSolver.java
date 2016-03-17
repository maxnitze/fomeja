package de.uni_bremen.agra.fomeja;

/* imports */
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.Prover;
import de.uni_bremen.agra.fomeja.backends.datatypes.ConstraintParameterList;
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
		List<Method> constraintMethods = RefactoringUtils.getConstraintMethods(component.getClass());

		for (Method method : constraintMethods) {
			int parameterCount = method.getGenericParameterTypes().length;

			ConstraintParameterList constraintParameterList = new ConstraintParameterList(parameterCount);
			List<Field>[] parameterFields = RefactoringUtils.getCollectionFieldsForMethod(method);
			for (int i=0; i<parameterCount; i++)
				constraintParameterList.add(i, component, parameterFields[i]);

			if (!constraintParameterList.isIncrementable())
				continue;

			Object[] methodParams = new Object[parameterCount];
			do {
				for (int i=0; i<parameterCount; i++)
					methodParams[i] = constraintParameterList.get(i).getCurrentCollectionObject();

				boolean accessibility = method.isAccessible();
				method.setAccessible(true);
				try {
					if (!(Boolean) method.invoke(component, methodParams))
						return false;
				} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
					String message = "could not invoke method \"" + method.getName() + "(" + Arrays.toString(methodParams) + ")\": " + e.getMessage();
					Logger.getLogger(FomejaSolver.class).fatal(message);
					throw new IllegalArgumentException(message);
				} finally {
					method.setAccessible(accessibility);
				}
			} while (constraintParameterList.increment());
		}

		return true;
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
