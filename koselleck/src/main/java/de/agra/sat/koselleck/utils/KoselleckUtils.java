package de.agra.sat.koselleck.utils;

/** imports */
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
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
import de.agra.sat.koselleck.backends.datatypes.ConstraintParameter;
import de.agra.sat.koselleck.disassembling.Disassembler;
import de.agra.sat.koselleck.disassembling.datatypes.DisassembledMethod;
import de.agra.sat.koselleck.exceptions.NoCollectionFieldException;
import de.agra.sat.koselleck.exceptions.NoConstraintMethodException;
import de.agra.sat.koselleck.exceptions.NoSuchFieldForClassException;

/**
 * KoseleckUtils is a collection of helper methods for this project.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public abstract class KoselleckUtils {
	/** pattern for the inner text of two angle brackets */
	private static final Pattern genericPattern = Pattern.compile("(?i)(<)(?<genericClass>.*)(>)");
	
	/** regular expression for a text enclosed by angle brackets */
	private static final String bracketRegex = "(?i)(<.*>)";
	/** regular expression for a generic collection type */
	private static final String collectionTypeRegex = "^.*([^<]+)<(?<genericType>.*)>$";
	/** regular expression for a generic class type */
	private static final String genericTypeRegex = "^(class )?(?<genericType>.*)$";
	
	/**
	 * getConstraintMethods returns a list of all {@link Method}s of the given
	 *  class that are annotated as {@link Constraint}s.
	 * 
	 * @param clazz the class to get the Constraint-Methods from
	 * 
	 * @return a list of all methods of the given class that are annotated as
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
	 * @return a list of all fields of the given class and the classes of its
	 *  attributes that are annotated as Variables
	 */
	public static List<Field> getVariableFields(Class<?> clazz) {
		List<Field> fields = new ArrayList<Field>();
		
		/** already visited classes */
		Set<Class<?>> visitedClasses = new HashSet<Class<?>>();
		/** new classes found in the last while-loop */
		List<Class<?>> lastClasses = new ArrayList<Class<?>>();
		
		lastClasses.add(clazz);
		
		/** as long as there are new classes found */
		while(lastClasses.size() > 0) {
			List<Class<?>> currentClasses = new ArrayList<Class<?>>();
			
			for(Class<?> cls : lastClasses) {
				visitedClasses.add(cls);
				
				/** add all field types and generic types of those */
				for(Field field : cls.getDeclaredFields()) {
					currentClasses.add(field.getType());
					
					if(!field.getType().getName().equals(field.getGenericType().toString()))
						currentClasses.addAll(getGenericClasses(field.getGenericType().toString()));
				}
			}
			
			lastClasses.clear();
			
			/** add classes to lastClasses if not already visited */
			for(Class<?> cls : currentClasses)
				if(!visitedClasses.contains(cls))
					lastClasses.add(cls);
		}
		
		/** get variable fields of all visited classes */
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
	 * @param genericType the generic type declaration to extract the classes
	 *  from
	 * 
	 * @return a list of classes given in the generic type declaration
	 */
	public static List<Class<?>> getGenericClasses(String genericType) {
		List<Class<?>> classes = new ArrayList<Class<?>>();
		
		Matcher matcher = genericPattern.matcher(genericType);
		while(matcher.find()) {
			String replacedMatch = matcher.group("genericClass").replaceAll(bracketRegex, "");
			
			String[] genericClasses = replacedMatch.split(",");
			for(String genericClass : genericClasses) {
				try {
					classes.add(Class.forName(genericClass.trim()));
				} catch (ClassNotFoundException e) {
					Logger.getLogger(KoselleckUtils.class).error("class for name \""+ genericClass.trim() +"\" could not be found.");
				}
			}
			
			if(matcher.group("genericClass").matches(bracketRegex))
				classes.addAll(getGenericClasses(matcher.group("genericClass")));
		}
		
		return classes;
	}
	
	/**
	 * getCollectionFieldsForMethod returns an array of lists of the collection
	 *  fields that match the single parameters of the given method. If the
	 *  constraint annotation specifies fields those are exclusively added to
	 *  the list. Otherwise all matching collection fields are added.
	 * 
	 * @param method the method to get the collection fields for
	 * 
	 * @return an array of lists of the collection fields that match the single
	 *  parameters of the given method. If the constraint annotation specifies
	 *  fields those are exclusively added to the list. Otherwise all matching
	 *  collection fields are added.
	 */
	public static List<Field>[] getCollectionFieldsForMethod(Method method) {
		Constraint constraintAnnotation = method.getAnnotation(Constraint.class);
		if(constraintAnnotation == null) {
			Logger.getLogger(KoselleckUtils.class).fatal("method \"" + method.toGenericString() + "\" is not a constraint method");
			throw new NoConstraintMethodException(method);
		}
		
		Type[] methodParameterTypes = method.getGenericParameterTypes();
		
		Constraint.Field[] constraintFields = constraintAnnotation.fields();
		if(methodParameterTypes.length != constraintFields.length) {
			String message = "count of annotated fields of method \"" + method.toGenericString() + "\" does not match its parameter count";
			Logger.getLogger(KoselleckUtils.class).fatal(message);
			throw new IllegalArgumentException(message);
		}
		
		Class<?> declaringClass = method.getDeclaringClass();
		int parameterCount = method.getParameterTypes().length;
		
		List<Field>[] methodCollectionFields = new FieldList[parameterCount];
		for(int i=0; i<parameterCount; i++) {
			String constraintFieldName = constraintFields[i].value();
			/** empty field name */
			if(constraintFieldName == null || constraintFieldName.equals(""))
				methodCollectionFields[i] = getCollectionFields(declaringClass, methodParameterTypes[i]);
			/** field name set */
			else {
				Field collectionField = null;
				try {
					collectionField = declaringClass.getDeclaredField(constraintFieldName);
				} catch (NoSuchFieldException | SecurityException e) {
					Logger.getLogger(KoselleckUtils.class).fatal("no such field \"" + constraintFieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"");
					throw new NoSuchFieldForClassException(constraintFieldName, declaringClass);
				}
				
				if(collectionField == null) {
					Logger.getLogger(KoselleckUtils.class).fatal("no such field \"" + constraintFieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"");
					throw new NoSuchFieldForClassException(constraintFieldName, declaringClass);
				}
				
				if(!Collection.class.isAssignableFrom(collectionField.getType())) {
					Logger.getLogger(KoselleckUtils.class).fatal("field \"" + collectionField.getName() + "\" is not a collection field (assignable from Collection)");
					throw new NoCollectionFieldException(collectionField);
				}
				
				String genericCollectionFieldType = collectionField.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
				String methodParameterType = methodParameterTypes[i].toString().replaceAll(genericTypeRegex, "${genericType}");
				if(!genericCollectionFieldType.equals(methodParameterType)) {
					String message = "\"" + genericCollectionFieldType + "\" is not a collection of \"" + methodParameterType + "\"";
					Logger.getLogger(KoselleckUtils.class).fatal(message);
					throw new IllegalArgumentException(message);
				}
				
				methodCollectionFields[i] = new FieldList(collectionField);
			}
		}
		
		return methodCollectionFields;
	}
	
	/**
	 * getCollectionFields returns a list of fields of the given class that are
	 *  assignable from the class Collection and, if type is not {@code null},
	 *  thats type equals the given type.
	 * 
	 * @param clazz the class to get the fields from
	 * @param type the type of the collection field ({@code null} for all
	 *  types)
	 * 
	 * @return a list of Fields of the given class that are assignable from the
	 *  class Collection and, if type is not {@code null}, thats type equals
	 *  the given type
	 */
	public static FieldList getCollectionFields(Class<?> clazz, Type type) {
		FieldList collectionFields = new FieldList();
		
		for(Field field : clazz.getDeclaredFields()) {
			if(Collection.class.isAssignableFrom(field.getType())) {
				if(type != null) {
					String genericCollectionFieldTypeName = field.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
					String genericTypeName = type.toString().replaceAll(genericTypeRegex, "${genericType}");
					if(genericCollectionFieldTypeName.equals(genericTypeName))
						collectionFields.add(field);
				} else
					collectionFields.add(field);
			}
		}
		
		return collectionFields;
	}
	
	/**
	 * increment indices increments the indices of the given array of
	 *  constraint parameters.
	 * 
	 * @param constraintParameters the array of constraint parameters thats
	 *  indices have to be incremented
	 * 
	 * @return {@code true} if an index was incremented, {@code false} if there
	 *  is no more index to increment
	 */
	public static boolean incrementIndices(ConstraintParameter[] constraintParameters) {
		return incrementIndices(constraintParameters, constraintParameters.length-1);
	}
	
	/**
	 * increment indices increments the indices of the given array of
	 *  constraint parameters at the position index. If this specific
	 *  constraint parameter can not be incremented anymore the indices at the
	 *  current index are reseted and the next index is incremented.
	 * 
	 * @param constraintParameters the array of constraint parameters thats
	 *  indices have to be incremented
	 * @param index
	 * 
	 * @return {@code true} if an index was incremented, {@code false} if there
	 *  is no more index to increment
	 */
	private static boolean incrementIndices(ConstraintParameter[] constraintParameters, int index) {
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
	 * getDisassembledMethod disassembles the given method and returns the byte
	 *  code (disassembled by javap).
	 * 
	 * @param method the method to disassemble
	 * 
	 * @return the disassembled method (disassembled by javap)
	 */
	public static DisassembledMethod getDisassembledMethod(Method method) {
		/** disassemble class */
		String disassembledClass = getDisassembledClass(method.getDeclaringClass());
		
		/** create method signature string */
		StringBuilder methodSignature = new StringBuilder();
		methodSignature.append(Modifier.toString(method.getModifiers()));
		methodSignature.append(" ");
		methodSignature.append(method.getReturnType().getCanonicalName());
		methodSignature.append(" ");
		methodSignature.append(method.getName());
		methodSignature.append("(");
		boolean firstParameterType = true;
		for(Class<?> cls : method.getParameterTypes()) {
			if(!firstParameterType)
				methodSignature.append(", ");
			else
				firstParameterType = false;
			
			methodSignature.append(cls.getCanonicalName());
		}
		methodSignature.append(");");
		
		/** split methods */
		for(String methodCode : disassembledClass.toString().split("\n\n")) {
			StringBuilder trimmedMethod = new StringBuilder();
			/** split lines of the method */
			boolean signatureLine = true;
			for(String methodCodeLine : methodCode.split("\n")) {
				if(methodCodeLine.trim().matches("^(class|public class|}|Code:|Compiled).*"))
					continue;
				
				/** check for method with right signature */
				if(signatureLine && !methodCodeLine.trim().equals(methodSignature.toString()))
					break;
				else if(signatureLine) {
					signatureLine = false;
					continue;
				}
				
				/** append line of bytecode */
				trimmedMethod.append(methodCodeLine.trim());
				trimmedMethod.append("\n");
			}
			
			if(!signatureLine) {
				System.out.println(methodSignature.toString() + "\n" + trimmedMethod.toString());
				
				return Disassembler.disassemble(
						method.getDeclaringClass(),
						method,
						methodSignature.toString(),
						trimmedMethod.toString());
			}
		}
		
		/** could never happen, because the method defines the class to
		 * disassemble */
		throw new RuntimeException("something went terribly wrong!");
	}
	
	/**
	 * getDisassembledConstraintMethods returns a map of method signatures to
	 *  disassembled methods containing the disassembled java byte code
	 *  (disassembled by javap) of the methods of the given class.
	 *  
	 * @param componentClass the class to disassemble the constraint methods
	 *  from
	 * 
	 * @return a map of method signatures to DisassembledMethods, containing
	 *  the disassembled java byte code (disassembled by javap) of the methods
	 *  of the given class.
	 */
	public static Map<String, DisassembledMethod> getDisassembledConstraintMethods(Class<?> componentClass) {
		String disassembledClass = getDisassembledClass(componentClass);
		
		List<Method> constraintMethods = getConstraintMethods(componentClass);
		Map<String, DisassembledMethod> disassembledMethods = new HashMap<String, DisassembledMethod>();
		
		for(String methodCode : disassembledClass.toString().split("\n\n")) {
			String trimmedMethodSignature = "";
			StringBuilder trimmedMethod = new StringBuilder();
			for(String methodCodeLine : methodCode.split("\n")) {
				if(!(methodCodeLine.trim().matches("^(class|public class|}|Code:).*"))) {
					if(methodCodeLine.trim().matches("^(public )?boolean .*"))
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
				disassembledMethods.put(trimmedMethodSignature, Disassembler.disassemble(componentClass, method, trimmedMethodSignature, trimmedMethod.toString()));
		}
		
		return disassembledMethods;
	}
	
	/** private methods
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * getDisassembledClass returns class disassembled by javap.
	 * 
	 * @param componentClass the class to disassemble
	 * 
	 * @return the class disassembled by javap
	 */
	private static String getDisassembledClass(Class<?> componentClass) {
		StringBuilder command = new StringBuilder("javap -classpath / -c ");
		if(componentClass.getProtectionDomain().getCodeSource() == null) {
			System.out.println(KoselleckUtils.class.getResource(""));
		}
		
		command.append(componentClass.getProtectionDomain().getCodeSource().getLocation().getPath());
		command.append(componentClass.getName().replaceAll("\\.", "/"));
		
		Process p = null;
		try {
			p = Runtime.getRuntime().exec(command.toString());
			return IOUtils.readFromStream(p.getInputStream());
		} catch (IOException e) {
			String message = "could not read class file for class \"" + componentClass.getSimpleName() + "\"";
			Logger.getLogger(KoselleckUtils.class).fatal(message);
			throw new IllegalArgumentException(message);
		} finally {
			if(p != null)
				p.destroy();
		}
	}
	
	/** inherited classes
	 * ----- ----- ----- ----- ----- */
	
	/**
	 * FieldList is a wrapper class for an array list of fields.
	 * 
	 * @version 1.0.0
	 * @author Max Nitze
	 */
	private static class FieldList extends ArrayList<Field> {
		/** serial id */
		private static final long serialVersionUID = 9039339410227929904L;
		
		/**
		 * Constructor for a new field list.
		 * 
		 * @param fields the fields to add to the list initially
		 */
		public FieldList(Field... fields) {
			for(Field f : fields)
				add(f);
		}
	}
}
