package de.agra.sat.koselleck;

/** imports */
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.Prover;
import de.agra.sat.koselleck.backends.Z3SMTIIJava;
import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.backends.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.decompiling.Decompiler;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralClass;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintLiteralObject;
import de.agra.sat.koselleck.decompiling.constraintvaluetypes.AbstractConstraintValue;
import de.agra.sat.koselleck.disassembling.bytecodetypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.NotSatisfiableException;
import de.agra.sat.koselleck.types.Opcode;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * I2AL implements methods to validate, satisfy, minimize and maximize a given
 *  object. 
 * 
 * @version 0.9.5
 * @author Max Nitze
 */
public abstract class DIAB {
	/** instance of the theorem prover to use */
	private static final Prover<?> prover = new Z3SMTIIJava();

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
		List<Method> constraintMethods = KoselleckUtils.getConstraintMethods(component.getClass());

		for (Method method : constraintMethods) {
			int parameterCount = method.getGenericParameterTypes().length;

			ConstraintParameter[] constraintParameters = new ConstraintParameter[parameterCount];
			List<Field>[] parameterFields = KoselleckUtils.getCollectionFieldsForMethod(method);
			for (int i=0; i<parameterCount; i++)
				constraintParameters[i] = new ConstraintParameter(component, i, parameterFields[i]);

			boolean skipTheorem = false;
			for (ConstraintParameter constraintParameter : constraintParameters) {
				if (!constraintParameter.isIncrementable()) {
					skipTheorem = true;
					break;
				}
			}
			if (skipTheorem)
				continue;

			Object[] methodParams = new Object[parameterCount];
			do {
				for (int i=0; i<parameterCount; i++)
					methodParams[i] = constraintParameters[i].getCurrentCollectionObject();

				boolean accessibility = method.isAccessible();
				method.setAccessible(true);
				try {
					if (!(Boolean) method.invoke(component, methodParams))
						return false;
				} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
					String message = "could not invoke method \"" + method.getName() + "\"";
					Logger.getLogger(DIAB.class).fatal(message);
					throw new IllegalArgumentException(message);
				} finally {
					method.setAccessible(accessibility);
				}
			} while (KoselleckUtils.incrementIndices(constraintParameters));
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
	public static boolean satisfy(Object component) {
		List<Method> constraintMethods = KoselleckUtils.getConstraintMethods(component.getClass());
		if (constraintMethods.size() <= 0)
			return true;

		List<Field> variableFields = KoselleckUtils.getVariableFields(component.getClass());
		if (variableFields.size() > 0) {
			Map<String, DisassembledMethod> disassembledMethods = KoselleckUtils.getDisassembledConstraintMethods(component.getClass());

			List<AbstractSingleTheorem> singleTheorems = new ArrayList<AbstractSingleTheorem>();

			for (Method method : constraintMethods) {
				List<Field>[] paramFields = KoselleckUtils.getCollectionFieldsForMethod(method);

				String methodSignature = (method.toGenericString().replaceFirst("^public boolean .*\\(", "public boolean "+ method.getName() +"(") + ";").replaceAll(", ", ",");;
				DisassembledMethod disassembledMethod = disassembledMethods.get(methodSignature);

				AbstractConstraintValue[] arguments = new AbstractConstraintValue[disassembledMethod.getMethod().getParameterTypes().length];
				for (int i = 0; i < arguments.length; i++)
					arguments[i] = new AbstractConstraintLiteralClass(
							disassembledMethod.getMethod().getParameterTypes()[i], Opcode.Xload, i+1);

				if (disassembledMethod != null)
					singleTheorems.add(new AbstractSingleTheorem(
							Decompiler.decompile(
									disassembledMethod, new AbstractConstraintLiteralObject(component), arguments), paramFields));
			}

			try {
				prover.solveAndAssign(component, singleTheorems);
			} catch (NotSatisfiableException e) {
				String message = "failed to satisfy given theorems due to:\n" + e.getMessage();
				System.err.println(message);
				Logger.getLogger(DIAB.class).info(message);
				return false;
			}
		}

		return validate(component);
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
		KoselleckUtils.getVariableFields(component.getClass());

		return -1;
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
		KoselleckUtils.getVariableFields(component.getClass());

		return -1;
	}
}
