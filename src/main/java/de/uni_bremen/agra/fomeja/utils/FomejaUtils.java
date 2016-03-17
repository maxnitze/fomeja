package de.uni_bremen.agra.fomeja.utils;

/* imports */
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.FomejaModel;
import de.uni_bremen.agra.fomeja.backends.datatypes.Constraint;
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

				Expression[] arguments = new Expression[disassembledMethod.getMethod().getParameterTypes().length];
				for (int i=0; i<arguments.length; i++)
					arguments[i] = new AtomClassExpr(disassembledMethod.getMethod().getParameterTypes()[i]);

				if (disassembledMethod != null) {
					StatementSeq resultStmtSeq = decompiler.decompile(
							disassembledMethod.getBytecodeLines(), 0, new AtomClassExpr(component.getClass()), arguments);
					if (resultStmtSeq.evalsToBoolExpr())
						constraint.addSingleConstraint(resultStmtSeq, paramFields);
					else {
						String message = "constraint method needs to be of boolean type but is \"" + resultStmtSeq.getResultType().getSimpleName() + "\"";
						Logger.getLogger(FomejaModel.class).fatal(message);
						throw new ModelException(message);
					}
				}
			}
		}

		constraint.unfoldConstraints(component);

		return constraint;
	}
}
