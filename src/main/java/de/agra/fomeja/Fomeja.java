package de.agra.fomeja;

/* imports */
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.fomeja.backends.Prover;
import de.agra.fomeja.backends.datatypes.Constraint;
import de.agra.fomeja.backends.datatypes.ConstraintParameterList;
import de.agra.fomeja.decompiling.Decompiler;
import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomObjectExpr;
import de.agra.fomeja.decompiling.statements.StatementSeq;
import de.agra.fomeja.disassembling.Disassembler;
import de.agra.fomeja.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.fomeja.exceptions.SatisfyException;
import de.agra.fomeja.utils.RefactoringUtils;

/**
 * COMMENT
 *
 * @version 0.9.5
 * @author Max Nitze
 */
public class Fomeja {
	/** COMMENT */
	private static Fomeja singleton;

	/** COMMENT */
	private Prover<?> prover;

	/**
	 * COMMENT
	 */
	private Fomeja() {
		this(FomejaDefaults.getDefaultProver());
	}

	/**
	 * COMMENT
	 * 
	 * @param prover
	 */
	private Fomeja(Prover<?> prover) {
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
	private boolean _validate(Object component) {
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
					Logger.getLogger(Fomeja.class).fatal(message);
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
	private boolean _satisfy(Object component) {
		if (RefactoringUtils.hasVariableFields(component.getClass())) {
			try {
				this.prover.solveAndAssign(this.getConstraintForComponent(component));
				return true;
			} catch (SatisfyException e) {
				String message = "failed to satisfy given theorems due to:\n" + e.getMessage();
				Logger.getLogger(Fomeja.class).info(message);
				return false;
			}
		} else {
			String message = "the component has no variable fields to satisfy";
			Logger.getLogger(Fomeja.class).info(message);
			throw new RuntimeException(message); // TODO change exception type
		}
	}

	/**
	 * minimize tries to satisfy the given component by calculating a
	 *  configuration for its variables that satisfies its constraints and
	 *  minimizes its objectives.
	 *
	 * @param component the component to satisfy with a minimum at its
	 *  objectives
	 *
	 * @return {@code -1}
	 */
	private int _minimize(Object component) {
		throw new RuntimeException("not implemented yet");
	}

	/**
	 * maximize tries to satisfy the given component by calculating a
	 *  configuration for its variables that satisfies its constraints and
	 *  maximizes its objectives.
	 *
	 * @param component the component to satisfy with a maximum at its
	 *  objectives
	 *
	 * @return {@code -1}
	 */
	private int _maximize(Object component) {
		throw new RuntimeException("not implemented yet");
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param component
	 * 
	 * @return
	 */
	private Constraint getConstraintForComponent(Object component) {
		Constraint constraint = new Constraint();

		List<Method> constraintMethods = RefactoringUtils.getConstraintMethods(component.getClass());
		Map<String, DisassembledMethod> disassembledMethods = Disassembler.disassemble(component.getClass());

		Decompiler decompiler = new Decompiler();
		for (Method method : constraintMethods) {
			List<Field>[] paramFields = RefactoringUtils.getCollectionFieldsForMethod(method);

			String methodSignature = (method.toGenericString().replaceFirst("^(public|private) boolean .*\\(", "$1 boolean "+ method.getName() +"(") + ";").replaceAll(", ", ",");
			DisassembledMethod disassembledMethod = disassembledMethods.get(methodSignature);

			Expression[] arguments = new Expression[disassembledMethod.getMethod().getParameterTypes().length];
			for (int i=0; i<arguments.length; i++)
				arguments[i] = new AtomClassExpr(disassembledMethod.getMethod().getParameterTypes()[i]);

			if (disassembledMethod != null) {
				StatementSeq resultStmtSeq = decompiler.decompile(
						disassembledMethod.getBytecodeLines(), 0, new AtomObjectExpr(component), arguments);
				if (resultStmtSeq.evalsToBoolExpr())
					constraint.addSingleConstraint(resultStmtSeq, paramFields);
				else {
					String message = "constraint method needs to be of boolean type but is \"" + resultStmtSeq.getResultType().getSimpleName() + "\"";
					Logger.getLogger(Fomeja.class).info(message);
					throw new IllegalArgumentException(message);
				}
			}
		}

		constraint.unfoldConstraints(component);

		return constraint;
	}

	/** static methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private static Fomeja getSingleton() {
		if (singleton == null)
			singleton = new Fomeja();
		return singleton;
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
	public static boolean validate(Object component) {
		return getSingleton()._validate(component);
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
	public static boolean satisfy(Object component) {
		return getSingleton()._satisfy(component);
	}

	/**
	 * minimize tries to satisfy the given component by calculating a
	 *  configuration for its variables that satisfies its constraints and
	 *  minimizes its objectives.
	 *
	 * @param component the component to satisfy with a minimum at its
	 *  objectives
	 *
	 * @return {@code -1}
	 */
	public static int minimize(Object component) {
		return getSingleton()._minimize(component);
	}

	/**
	 * maximize tries to satisfy the given component by calculating a
	 *  configuration for its variables that satisfies its constraints and
	 *  maximizes its objectives.
	 *
	 * @param component the component to satisfy with a maximum at its
	 *  objectives
	 *
	 * @return {@code -1}
	 */
	public static int maximize(Object component) {
		return getSingleton()._maximize(component);
	}
}
