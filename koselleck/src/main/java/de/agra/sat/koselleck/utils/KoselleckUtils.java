package de.agra.sat.koselleck.utils;

/** imports */
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.annotations.Constraint;
import de.agra.sat.koselleck.annotations.Variable;
import de.agra.sat.koselleck.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.disassembling.Disassembler;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;

/**
 * 
 * @author Max Nitze
 */
public abstract class KoselleckUtils {
	/** pattern for the inner text of two angle brackets */
	private static final Pattern genericPattern = Pattern.compile("(?i)(<)(.*)(>)");
	/** pattern for a text enclosed by angle brackets */
;	private static final Pattern bracketPattern = Pattern.compile("(?i)(<.*>)");
	/**  */
	private static final String collectionTypeRegex = "^.*([^<]+)<(?<genericType>.*)>$";
	/**  */
	private static final String genericTypeRegex = "^(class )?(?<genericType>.*)$";
	
	/**
	 * getConstraintMethods returns a list of all {@link Method}s of the given
	 *  class that are annotated as {@link Constraint}s.
	 * 
	 * @param clazz the class to get the Constraint-Methods from
	 * 
	 * @return a list of all Methods of the given class that are annotated as
	 *  Constraints
	 */
	public static List<Method> getConstraintMethods(Class<?> clazz) {
		List<Method> methods = new ArrayList<Method>();
		
		for(Method method : clazz.getDeclaredMethods())
			if(method.getAnnotation(Constraint.class) != null)
				methods.add(method);
		
		return methods;
	}
	
	/**
	 * getVariableFields returns a list of all {@link Field}s of the given
	 *  class and the classes of its attributes that are annotated as
	 *  {@link Variable}.
	 * 
	 * @param clazz the class to get the Variable-Fields from
	 * 
	 * @return a list of all Fields of the given class and the classes of its
	 *  attributes that are annotated as Variables
	 */
	public static List<Field> getVariableFields(Class<?> clazz) {
		List<Field> fields = new ArrayList<Field>();
		
		Set<Class<?>> visitedClasses = new HashSet<Class<?>>();
		List<Class<?>> lastClasses = new ArrayList<Class<?>>();
		
		lastClasses.add(clazz);
		
		while(lastClasses.size() > 0) {
			List<Class<?>> currentClasses = new ArrayList<Class<?>>();
			
			for(Class<?> cls : lastClasses) {
				visitedClasses.add(cls);
				
				for(Field field : cls.getDeclaredFields()) {
					currentClasses.add(field.getType());
					
					if(!field.getType().getName().equals(field.getGenericType().toString()))
						currentClasses.addAll(getGenericClasses(field.getGenericType().toString()));
				}
			}
			
			lastClasses.clear();
			
			for(Class<?> cls : currentClasses)
				if(!visitedClasses.contains(cls))
					lastClasses.add(cls);
		}
		
		for(Class<?> cls : visitedClasses)
			for(Field field : cls.getDeclaredFields())
				if(field.getAnnotation(Variable.class) != null)
					fields.add(field);
		
		return fields;
	}
	
	/**
	 * getGenericClasses returns a list of classes given in the generic type
	 *  declaration.
	 * 
	 * @param genericType the type generic declaration to extract the classes
	 *  from
	 * 
	 * @return a list of classes given in the generic type declaration
	 */
	public static List<Class<?>> getGenericClasses(String genericType) {
		List<Class<?>> classes = new ArrayList<Class<?>>();
		
		Matcher matcher = genericPattern.matcher(genericType);
		
		while(matcher.find()) {
			String replacedMatch = matcher.group(2).replaceAll(bracketPattern.pattern(), "");
			
			String[] genericClasses = replacedMatch.split(",");
			for(String genericClass : genericClasses) {
				try {
					classes.add(Class.forName(genericClass.trim()));
				} catch (ClassNotFoundException e) {
					System.err.println("class for name \""+ genericClass.trim() +"\" could not be found.\n" + e.getMessage()); // TODO logging
				}
			}
			
			if(matcher.group(2).matches(bracketPattern.pattern()))
				classes.addAll(getGenericClasses(matcher.group(2)));
		}
		
		return classes;
	}
	
	/**
	 * 
	 * @param method
	 * 
	 * @return
	 */
	public static List<Field>[] getCollectionFieldsForMethod(Method method) {
		Constraint constraintAnnotation = method.getAnnotation(Constraint.class);
		if(constraintAnnotation == null)
			throw new IllegalArgumentException("no constraint method"); // TODO other exception
		
		Type[] methodParameterTypes = method.getGenericParameterTypes();
		
		Constraint.Field[] constraintFields = constraintAnnotation.fields();
		if(methodParameterTypes.length != constraintFields.length)
			throw new IllegalArgumentException("different parameter counts"); // TODO other exception
		
		Class<?> declaringClass = method.getDeclaringClass();
		int parameterCount = method.getParameterTypes().length;
		
		List<Field>[] methodCollectionFields = new FieldList[parameterCount];
		for(int i=0; i<parameterCount; i++) {
			String constraintFieldName = constraintFields[i].name();
			if(constraintFieldName == null || constraintFieldName.equals(""))
				methodCollectionFields[i] = getCollectionFields(declaringClass, methodParameterTypes[i]);
			else {
				Field collectionField = null;
				try {
					collectionField = declaringClass.getDeclaredField(constraintFieldName);
				} catch (NoSuchFieldException | SecurityException e) {
					throw new IllegalArgumentException("no such field \"" + constraintFieldName + "\""); // TODO other exception
				}
				
				if(collectionField == null)
					throw new IllegalArgumentException("no such field \"" + constraintFieldName + "\""); // TODO other exception
				
				if(!Collection.class.isAssignableFrom(collectionField.getType()))
					throw new IllegalArgumentException("no collection field"); // TODO other exception
				
				String genericCollectionFieldType = collectionField.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
				String methodParameterType = methodParameterTypes[i].toString().replaceAll(genericTypeRegex, "${genericType}");
				if(!genericCollectionFieldType.equals(methodParameterType))
					throw new IllegalArgumentException("not a collecton of parameter type"); // TODO other exception
				
				methodCollectionFields[i] = new FieldList(collectionField);
			}
		}
		
		return methodCollectionFields;
	}
	
	/**
	 * getCollectionFields returns a list of {@link Field}s of the given class
	 *  that are assignable from the class {@link Collection}.
	 * 
	 * @param clazz the class to get the fields from
	 * @param type
	 * 
	 * @return a list of Fields of the given class that are assignable from the
	 *  class Collection
	 */
	public static FieldList getCollectionFields(Class<?> clazz, Type type) {
		FieldList collectionFields = new FieldList();
		
		for(Field field : clazz.getDeclaredFields()) {
			if(Collection.class.isAssignableFrom(field.getType())) {
				String genericCollectionFieldTypeName = field.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
				String genericTypeName = type.toString().replaceAll(genericTypeRegex, "${genericType}");
				if(genericCollectionFieldTypeName.equals(genericTypeName))
					collectionFields.add(field);
			}
		}
		
		return collectionFields;
	}
	
	/**
	 * 
	 * @param constraintParameters
	 * 
	 * @return
	 */
	public static boolean incrementIndices(ConstraintParameter[] constraintParameters) {
		return incrementIndices(constraintParameters, constraintParameters.length-1);
	}
	
	/**
	 * 
	 * @param constraintParameters
	 * @param index
	 * 
	 * @return
	 */
	public static boolean incrementIndices(ConstraintParameter[] constraintParameters, int index) {
		if(!constraintParameters[index].incrementIndex()) {
			if(index > 0) {
				constraintParameters[index].resetIndex();
				return incrementIndices(constraintParameters, index-1);
			} else
				return false;
		} else
			return true;
	}
	
	/**
	 * getDisassembledConstraintMethods returns a map of method signatures to
	 *  {@link DisassembledMethod}s, containing the disassembled java bytecode
	 *  (disassembled by javap) of the methods of the given class.
	 *  
	 * @param component
	 * 
	 * @return a map of method signatures to DisassembledMethods, containing
	 *  the disassembled java bytecode (disassembled by javap) of the methods
	 *  of the given class.
	 */
	public static Map<String, DisassembledMethod> getDisassembledConstraintMethods(Object component) {
		List<Method> constraintMethods = getConstraintMethods(component.getClass());
		
		Map<String, DisassembledMethod> disassembledMethods = new HashMap<String, DisassembledMethod>();
		
		StringBuilder command = new StringBuilder("javap -classpath / -c ");
		command.append(component.getClass().getProtectionDomain().getCodeSource().getLocation().getPath());
		command.append(component.getClass().getName().replaceAll("\\.", "/"));

		Process p = null;
		try {
			p = Runtime.getRuntime().exec(command.toString());
		} catch (IOException e) {
			String message = "could not read class file for class \"" + component.getClass().getSimpleName() + "\"";
			Logger.getLogger(KoselleckUtils.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
		String disassembledCode = IOUtils.readFromStream(p.getInputStream());
		
		for(String methodCode : disassembledCode.toString().split("\n\n")) {
			String trimmedMethodSignature = "";
			StringBuilder trimmedMethod = new StringBuilder();
			for(String methodCodeLine : methodCode.split("\n")) {
				if(!(methodCodeLine.trim().matches("^(class|public class|}|Code:).*"))) {
					if(methodCodeLine.trim().matches("^(public )?(boolean|int) .*"))
						trimmedMethodSignature = methodCodeLine.trim().replaceAll(", ", ",");
					else {
						trimmedMethod.append(methodCodeLine.trim());
						trimmedMethod.append("\n");
					}
				}
			}
			
			boolean skip = true;
			Method method = null;
			for(Method m : constraintMethods) {
				if((m.toGenericString().replaceAll(" \\S*\\.([^\\.]+)\\(", " $1(") + ";").replaceAll(", ", ",").equals(trimmedMethodSignature)) {
					method = m;
					skip = false;
					break;
				}
			}
			
			if(!skip && trimmedMethodSignature != "")
				disassembledMethods.put(trimmedMethodSignature, Disassembler.disassemble(component, method, trimmedMethodSignature, trimmedMethod.toString()));
		}
		
		return disassembledMethods;
	}
	
	/**
	 * 
	 * @author Max Nitze
	 */
	public static class FieldList extends ArrayList<Field> {
		/**  */
		private static final long serialVersionUID = 9039339410227929904L;
		
		/**
		 * 
		 * @param fields
		 */
		public FieldList(Field... fields) {
			for(Field f : fields)
				add(f);
		}
	}
}
