package de.uni_bremen.agra.fomeja.utils;

/** imports */
import java.util.List;

/**
 * ListUtils provides (mainly comparing) functions for lists and arrays.
 * 
 * @author Max Nitze
 */
public final class CompareUtils {
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
	 * 
	 * @param <T> COMMENT
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
	 * 
	 * @param <T> COMMENT
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
	 * 
	 * @param <T> COMMENT
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
	 * 
	 * @param <T> COMMENT
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
	 * 
	 * @param <T> COMMENT
	 */
	public static <T extends Comparable<T>> boolean isBetween(T value, T start, T end) {
		/** compare the value to the borders of the area */
		if (start.compareTo(value) <= 0 && end.compareTo(value) >= 0)
			return true;
		else
			return false;
	}
}
