package de.agra.sat.koselleck.utils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ClassUtils {
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
	private ClassUtils() {}

	/**
	 * COMMENT
	 * 
	 * @param class1
	 * @param class2
	 * 
	 * @return
	 */
	public static boolean classesEquals(Class<?> class1, Class<?> class2) {
		if (CompareUtils.equalsAny(class1, doubleClasses))
			return CompareUtils.equalsAny(class2, doubleClasses);
		else if (CompareUtils.equalsAny(class1, floatClasses))
			return CompareUtils.equalsAny(class2, floatClasses);
		else if (CompareUtils.equalsAny(class1, integerClasses))
			return CompareUtils.equalsAny(class2, integerClasses);
		else
			return class1.equals(class2);
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean isBasicClass(Class<?> clazz) {
		return isDoubleClass(clazz)
				|| isFloatClass(clazz)
				|| isIntegerClass(clazz)
				|| isBooleanClass(clazz);
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean isDoubleClass(Class<?> clazz) {
		return CompareUtils.equalsAny(clazz, doubleClasses);
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean isFloatClass(Class<?> clazz) {
		return CompareUtils.equalsAny(clazz, floatClasses);
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean isIntegerClass(Class<?> clazz) {
		return CompareUtils.equalsAny(clazz, integerClasses);
	}

	/**
	 * COMMENT
	 * 
	 * @param clazz
	 * 
	 * @return
	 */
	public static boolean isBooleanClass(Class<?> clazz) {
		return CompareUtils.equalsAny(clazz, booleanClasses);
	}
}
