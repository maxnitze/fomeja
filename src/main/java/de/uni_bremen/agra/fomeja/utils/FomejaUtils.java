package de.uni_bremen.agra.fomeja.utils;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.backends.datatypes.Constraint;
import de.uni_bremen.agra.fomeja.backends.datatypes.ConstraintParameterList;
import de.uni_bremen.agra.fomeja.decompiling.Decompiler;
import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomClassExpr;
import de.uni_bremen.agra.fomeja.decompiling.statements.StatementSeq;
import de.uni_bremen.agra.fomeja.disassembling.Disassembler;
import de.uni_bremen.agra.fomeja.disassembling.bytecodetypes.DisassembledMethod;
import de.uni_bremen.agra.fomeja.exceptions.ModelException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public final class FomejaUtils {
	/**
	 * COMMENT
	 */
	private FomejaUtils() {}



	/**
	 * COMMENT
	 *
	 * @param component COMMENT
	 *
	 * @return COMMENT
	 */
	public static boolean validate(Object component) {
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
					Logger.getLogger(FomejaUtils.class).fatal(message);
					throw new IllegalArgumentException(message);
				} finally {
					method.setAccessible(accessibility);
				}
			} while (constraintParameterList.increment());
		}

		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param component COMMENT
	 * 
	 * @return COMMENT
	 */
	public static Constraint getConstraintForComponent(Object component) {
		Constraint constraint = new Constraint();
		List<Method> constraintMethods = RefactoringUtils.getConstraintMethods(component.getClass());		
		if (RefactoringUtils.hasVariableFields(component.getClass())) {
			Map<String, DisassembledMethod> disassembledMethods = Disassembler.disassemble(component.getClass());

			Decompiler decompiler = new Decompiler();
			for (Method method : constraintMethods) {
				List<Field>[] paramFields = RefactoringUtils.getCollectionFieldsForMethod(method);

				String methodSignature = (method.toGenericString().replaceFirst("^(public|private) boolean .*\\(", "$1 boolean "+ method.getName() +"(") + ";").replaceAll(", ", ",");;
				DisassembledMethod disassembledMethod = disassembledMethods.get(methodSignature);
				if (disassembledMethod != null) {
					Expression[] arguments = new Expression[disassembledMethod.getMethod().getParameterTypes().length];
					for (int i=0; i<arguments.length; i++)
						arguments[i] = new AtomClassExpr(disassembledMethod.getMethod().getParameterTypes()[i]);

					StatementSeq resultStmtSeq = decompiler.decompile(
							disassembledMethod.getBytecodeLines(), 0, new AtomClassExpr(component.getClass()), arguments);
					if (resultStmtSeq.evalsToBoolExpr())
						constraint.addSingleConstraint(resultStmtSeq, paramFields);
					else {
						String message = "constraint method needs to be of boolean type but is \"" + resultStmtSeq.getResultType().getSimpleName() + "\"";
						Logger.getLogger(FomejaUtils.class).fatal(message);
						throw new ModelException(message);
					}
				}
			}
		}

		constraint.unfoldConstraints(component);

		return constraint;
	}
}
