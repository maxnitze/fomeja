package de.agra.sat.koselleck;

/** imports */
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.backends.TheoremProver;
import de.agra.sat.koselleck.backends.datatypes.AbstractSingleTheorem;
import de.agra.sat.koselleck.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.decompiling.Decompiler;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.NotSatisfyableException;
import de.agra.sat.koselleck.utils.KoselleckUtils;

/**
 * I2AL implements methods to validate, satisfy, minimize and maximize 
 * 
 * @author Max Nitze
 * @version 0.8.5
 */
public abstract class I2AL {
	/** instance of the theorem prover to use */
	private static final TheoremProver theoremProver = new de.agra.sat.koselleck.backends.Z3();
	
	/**
	 * validate validates a given component by checking its constraints with a
	 *  given configuration.
	 * 
	 * @param component the component to validate
	 * 
	 * @return {@code true} if the given configuration matches the constraints
	 *  of the components class, {@code false} otherwise
	 * 
	 * @throws IllegalArgumentException if there is a constraint method that
	 *  can't be invoked with the given parameters
	 */
	public static boolean validate(Object component) {
		List<Method> constraintMethods = KoselleckUtils.getConstraintMethods(component.getClass());
		
		for(Method method : constraintMethods) {
			int parameterCount = method.getGenericParameterTypes().length;
			
			ConstraintParameter[] constraintParameters = new ConstraintParameter[parameterCount];
			List<Field>[] parameterFields = KoselleckUtils.getCollectionFieldsForMethod(method);
			for(int i=0; i<parameterCount; i++)
				constraintParameters[i] = new ConstraintParameter(component, i, parameterFields[i]);
			
			boolean skipTheorem = false;
			for(ConstraintParameter constraintParameter : constraintParameters) {
				if(!constraintParameter.isIncrementable()) {
					skipTheorem = true;
					break;
				}
			}
			if(skipTheorem)
				continue;
			
			Object[] methodParams = new Object[parameterCount];
			do {
				for(int i=0; i<parameterCount; i++)
					methodParams[i] = constraintParameters[i].getCurrentCollectionObject();
				
				method.setAccessible(true);
				try {
					if(!(Boolean)method.invoke(component, methodParams))
						return false;
				} catch (IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
					Logger.getLogger(I2AL.class).fatal("could not invoke method \"" + method.getName() + "\"");
					throw new IllegalArgumentException("could not invoke method \"" + method.getName() + "\"");
				}
			} while(KoselleckUtils.incrementIndices(constraintParameters));
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
		if(constraintMethods.size() <= 0)
			return true;
		
		List<Field> variableFields = KoselleckUtils.getVariableFields(component.getClass());
		if(variableFields.size() > 0) {
			theoremProver.setComponent(component);
			
			Map<String, DisassembledMethod> disassembledMethods = KoselleckUtils.getDisassembledConstraintMethods(component);
			
			List<AbstractSingleTheorem> singleTheorems = new ArrayList<AbstractSingleTheorem>();
			
			for(Method method : constraintMethods) {
				List<Field>[] paramFields = KoselleckUtils.getCollectionFieldsForMethod(method);
				
				String methodSignature = (method.toGenericString().replaceFirst("^public boolean .*\\(", "public boolean "+ method.getName() +"(") + ";").replaceAll(", ", ",");;
				DisassembledMethod disassembledMethod = disassembledMethods.get(methodSignature);
				
//				System.out.println(disassembledMethod.toString() + "\n"); // TODO delete output of disassembled method
				
				if(disassembledMethod != null)
					singleTheorems.add(new AbstractSingleTheorem(Decompiler.decompile(disassembledMethod), paramFields));
			}
			
			try {
				theoremProver.solveAndAssign(singleTheorems);
			} catch (NotSatisfyableException e) {
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
		theoremProver.setComponent(component);
		
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
		theoremProver.setComponent(component);
		
		KoselleckUtils.getVariableFields(component.getClass());
		
		return -1;
	}
}
