package de.agra.sat.koselleck.utils;

/** imports */
import java.util.List;

/**
 * ListUtils provides (mainly comparing) functions for lists and arrays.
 * 
 * @author Max Nitze
 */
public final class CompareUtils {
	/** array of the two boolean classes */
	public static final Class<?>[] booleanClasses = new Class<?>[] { boolean.class, Boolean.class };
	/** array of the two double classes */
	public static final Class<?>[] doubleClasses = new Class<?>[] { double.class, Double.class };
	/** array of the two float classes */
	public static final Class<?>[] floatClasses = new Class<?>[] { float.class, Float.class };
	/** array of the two integer classes */
	public static final Class<?>[] integerClasses = new Class<?>[] { int.class, Integer.class };

	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private CompareUtils() {}

	/**
	 * identsAny compares a given element with all elements of a given array.
	 *  If an array element is identical to the given element {@code true} is
	 *  returned, otherwise the return value is {@code false}.
	 * 
	 * @param element the element to look for
	 * @param array the array to look over
	 * 
	 * @return {@code true} if there is an element in the array, that is
	 *  identical to the given element, {@code false} otherwise
	 */
	public static <T> boolean identsAny(T element, T[] array){
		for (T e : array)
			if (e == element)
				return true;
		return false;
	}

	/**
	 * identsAny compares a given element with all elements of a given list.
	 *  If a list element is identical to the given element {@code true} is
	 *  returned, otherwise the return value is {@code false}.
	 * 
	 * @param element the element to look for
	 * @param list the list to look over
	 * 
	 * @return {@code true} if there is an element in the list, that is
	 *  identical to the given element, {@code false} otherwise
	 */
	public static <T> boolean identsAny(T element, List<T> list){
		for (T e : list)
			if (e == element)
				return true;
		return false;
	}

	/**
	 * equalsAny compares a given element with all elements of a given array.
	 *  If an array element is equal to the given element {@code true} is
	 *  returned, otherwise the return value is {@code false}.
	 * 
	 * @param element the element to look for
	 * @param array the array to look over
	 * 
	 * @return {@code true} if there is an element in the array, that is
	 *  equal to the given element, {@code false} otherwise
	 */
	public static <T> boolean equalsAny(T element, T[] array) {
		for (T e : array)
			if (e.equals(element))
				return true;
		return false;
	}

	/**
	 * equalsAny compares a given element with all elements of a given list.
	 *  If a list element is equal to the given element {@code true} is
	 *  returned, otherwise the return value is {@code false}.
	 * 
	 * @param element the element to look for
	 * @param list the list to look over
	 * 
	 * @return {@code true} if there is an element in the list, that is
	 *  equal to the given element, {@code false} otherwise
	 */
	public static <T> boolean equalsAny(T element, List<T> list) {
		for (T e : list)
			if (e.equals(element))
				return true;
		return false;
	}

	/**
	 * instanceofAny checks if the given object is instance of any of the
	 *  classes given by the classes array.
	 * 
	 * @param object the object to check
	 * @param classes the array of classes to check the object against
	 * 
	 * @return {@code true} if the object is instance of any of the classes
	 *  of the given classes array, {@code false} otherwise
	 */
	public static boolean instanceofAny(Object object, Class<?>[] classes) {
		for (Class<?> clazz : classes)
			if (clazz.isInstance(object))
				return true;
		return false;
	}

	/**
	 * instanceofAny checks if the given object is instance of any of the
	 *  classes given by the classes list.
	 * 
	 * @param object the object to check
	 * @param classes the list of classes to check the object against
	 * 
	 * @return {@code true} if the object is instance of any of the classes
	 *  of the given classes list, {@code false} otherwise
	 */
	public static boolean instanceofAny(Object object, List<Class<?>> classes) {
		for (Class<?> clazz : classes)
			if (clazz.isInstance(object))
				return true;
		return false;
	}

	/**
	 * isBetween returns {@code true} if the given value is greater or equal
	 *  to the given start and lower or equal to the given end, {@code false}
	 *  else.
	 * 
	 * @param value the value to compare to the borders
	 * @param start the first value of the area
	 * @param end the last value of the area
	 * 
	 * @return {@code true} if the given value is greater or equal to the given
	 *  start and lower or equal to the given end, {@code false} else.
	 */
	public static <T extends Comparable<T>> boolean isBetween(T value, T start, T end) {
		/** compare the value to the borders of the area */
		if (start.compareTo(value) <= 0 && end.compareTo(value) >= 0)
			return true;
		else
			return false;
	}

	/**
	 * 
	 * @param class1
	 * @param class2
	 * 
	 * @return
	 */
	public static boolean classesEquals(Class<?> class1, Class<?> class2) {
		if (equalsAny(class1, doubleClasses))
			return equalsAny(class2, doubleClasses);
		else if (equalsAny(class1, floatClasses))
			return equalsAny(class2, floatClasses);
		else if (equalsAny(class1, integerClasses))
			return equalsAny(class2, integerClasses);
		else
			return class1.equals(class2);
	}
}
