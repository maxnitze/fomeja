package de.uni_bremen.agra.fomeja.utils;

/* imports */
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.annotations.Constraint;
import de.uni_bremen.agra.fomeja.annotations.Variable;
import de.uni_bremen.agra.fomeja.exceptions.RefactoringException;

/**
 * KoseleckUtils is a collection of helper methods for this project.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public final class RefactoringUtils {
	/** pattern for the inner text of two angle brackets */
	private static final Pattern genericPattern = Pattern.compile("(?i)(<)(?<genericClass>.*)(>)");

	/** regular expression for a text enclosed by angle brackets */
	private static final String bracketRegex = "(?i)(<.*>)";
	/** regular expression for a generic collection type */
	private static final String collectionTypeRegex = "^.*([^<]+)<(?<genericType>.*)>$";
	/** regular expression for a generic class type */
	private static final String genericTypeRegex = "^(class )?(?<genericType>.*)$";

	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private RefactoringUtils() {}

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

		for (Method method : clazz.getDeclaredMethods())
			if (method.getAnnotation(Constraint.class) != null)
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
		while (!lastClasses.isEmpty()) {
			List<Class<?>> currentClasses = new ArrayList<Class<?>>();

			for (Class<?> cls : lastClasses) {
				visitedClasses.add(cls);

				/** add all field types and generic types of those */
				for (Field field : cls.getDeclaredFields()) {
					currentClasses.add(field.getType());

					if (!field.getType().getName().equals(field.getGenericType().toString()))
						currentClasses.addAll(getGenericClasses(field.getGenericType().toString()));
				}
			}

			lastClasses.clear();

			/** add classes to lastClasses if not already visited */
			for (Class<?> cls : currentClasses)
				if (!visitedClasses.contains(cls))
					lastClasses.add(cls);
		}

		/** get variable fields of all visited classes */
		for (Class<?> cls : visitedClasses)
			for (Field field : cls.getDeclaredFields())
				if (field.getAnnotation(Variable.class) != null)
					fields.add(field);

		return fields;
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean hasVariableFields(Class<?> clazz) {
		/** already visited classes */
		Set<Class<?>> visitedClasses = new HashSet<Class<?>>();
		/** new classes found in the last while-loop */
		List<Class<?>> lastClasses = new ArrayList<Class<?>>();

		lastClasses.add(clazz);

		/** as long as there are new classes found */
		while (!lastClasses.isEmpty()) {
			List<Class<?>> currentClasses = new ArrayList<Class<?>>();

			for (Class<?> cls : lastClasses) {
				for (Field field : cls.getDeclaredFields())
					if (field.getAnnotation(Variable.class) != null)
						return true;

				visitedClasses.add(cls);

				/** add all field types and generic types of those */
				for (Field field : cls.getDeclaredFields()) {
					currentClasses.add(field.getType());

					if (!field.getType().getName().equals(field.getGenericType().toString()))
						currentClasses.addAll(getGenericClasses(field.getGenericType().toString()));
				}
			}

			lastClasses.clear();

			/** add classes to lastClasses if not already visited */
			for (Class<?> cls : currentClasses)
				if (!visitedClasses.contains(cls))
					lastClasses.add(cls);
		}

		return false;
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
		while (matcher.find()) {
			String replacedMatch = matcher.group("genericClass").replaceAll(bracketRegex, "");

			String[] genericClasses = replacedMatch.split(",");
			for (String genericClass : genericClasses) {
				try {
					classes.add(Class.forName(genericClass.trim()));
				} catch (ClassNotFoundException e) {
					Logger.getLogger(RefactoringUtils.class).error("class for name \""+ genericClass.trim() +"\" could not be found.");
				}
			}

			if (matcher.group("genericClass").matches(bracketRegex))
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
		if (constraintAnnotation == null) {
			Logger.getLogger(RefactoringUtils.class).fatal("method \"" + method.toGenericString() + "\" is not a constraint method");
			throw new RefactoringException("method \"" + method.toGenericString() + "\" is not a constraint method");
		}

		Type[] methodParameterTypes = method.getGenericParameterTypes();

		String[] constraintFields = constraintAnnotation.fields();
		if (constraintFields.length != 0 && methodParameterTypes.length != constraintFields.length) {
			String message = "count of annotated fields of method \"" + method.toGenericString() + "\" does not match its parameter count";
			Logger.getLogger(RefactoringUtils.class).fatal(message);
			throw new RefactoringException(message);
		}

		Class<?> declaringClass = method.getDeclaringClass();
		int parameterCount = method.getParameterTypes().length;

		List<Field>[] methodCollectionFields = new FieldList[parameterCount];
		for (int i=0; i<parameterCount; i++) {
			String constraintFieldName = constraintFields.length != 0 ? constraintFields[i] : null;
			/** empty field name */
			if (constraintFieldName == null || constraintFieldName.equals(""))
				methodCollectionFields[i] = getCollectionFields(declaringClass, methodParameterTypes[i]);
			/** field name set */
			else {
				Field collectionField = null;
				try {
					collectionField = declaringClass.getDeclaredField(constraintFieldName);
				} catch (NoSuchFieldException | SecurityException e) {
					String message = "no such field \"" + constraintFieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"";
					Logger.getLogger(RefactoringUtils.class).fatal(message);
					throw new RefactoringException(message);
				}

				if (collectionField == null) {
					String message = "no such field \"" + constraintFieldName + "\" for declaring class \"" + declaringClass.getCanonicalName() + "\"";
					Logger.getLogger(RefactoringUtils.class).fatal(message);
					throw new RefactoringException(message);
				}

				if (!Collection.class.isAssignableFrom(collectionField.getType())) {
					String message = "field \"" + collectionField.getName() + "\" is not a collection field (assignable from Collection)";
					Logger.getLogger(RefactoringUtils.class).fatal(message);
					throw new RefactoringException(message);
				}

				String genericCollectionFieldType = collectionField.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
				String methodParameterType = methodParameterTypes[i].toString().replaceAll(genericTypeRegex, "${genericType}");
				if (!genericCollectionFieldType.equals(methodParameterType)) {
					String message = "\"" + genericCollectionFieldType + "\" is not a collection of \"" + methodParameterType + "\"";
					Logger.getLogger(RefactoringUtils.class).fatal(message);
					throw new RefactoringException(message);
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

		for (Field field : clazz.getDeclaredFields()) {
			if (Collection.class.isAssignableFrom(field.getType())) {
				if (type != null) {
					String genericCollectionFieldTypeName = field.getGenericType().toString().replaceAll(collectionTypeRegex, "${genericType}");
					String genericTypeName = type.toString().replaceAll(genericTypeRegex, "${genericType}");
					if (genericCollectionFieldTypeName.equals(genericTypeName))
						collectionFields.add(field);
				} else
					collectionFields.add(field);
			}
		}

		return collectionFields;
	}

	/**
	 * COMMENT
	 * 
	 * @param cls
	 * @param methodName
	 * @param parameterTypes
	 * 
	 * @return
	 */
	public static Method getMethodForClass(Class<?> cls, String methodName, Class<?>... parameterTypes) {
		try {
			return cls.getMethod(methodName, parameterTypes);
		} catch(NoSuchMethodException | SecurityException e) {
			String message = "could not get method with name \"" + methodName + "\" from class \"" + cls.getSimpleName() + "\"";
			Logger.getLogger(RefactoringUtils.class).fatal(message);
			throw new RefactoringException(message);
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
			for (Field f : fields)
				add(f);
		}
	}
}
