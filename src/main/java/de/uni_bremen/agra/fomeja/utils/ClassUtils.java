package de.uni_bremen.agra.fomeja.utils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ClassUtils {
	/** array of the two boolean classes */
	public static final Class<?>[] booleanTypes = new Class<?>[] { boolean.class, Boolean.class };
	/** array of the two double classes */
	public static final Class<?>[] doubleTypes = new Class<?>[] { double.class, Double.class };
	/** array of the two float classes */
	public static final Class<?>[] floatTypes = new Class<?>[] { float.class, Float.class };
	/** array of the two integer classes */
	public static final Class<?>[] integerTypes = new Class<?>[] { int.class, Integer.class };
	/** array of the two integer classes */
	public static final Class<?>[] longTypes = new Class<?>[] { long.class, Long.class };
	/** array of the two integer classes */
	public static final Class<?>[] shortTypes = new Class<?>[] { short.class, Short.class };
	/** array of the two integer classes */
	public static final Class<?>[] charTypes = new Class<?>[] { char.class, Character.class };
	/** array of the two integer classes */
	public static final Class<?>[] byteTypes = new Class<?>[] { byte.class, Byte.class };

	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private ClassUtils() {}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static Class<?> mapToNonPrimitive(Class<?> type) {
		if (type.equals(boolean.class))
			return Boolean.class;
		else if (type.equals(double.class))
			return Double.class;
		else if (type.equals(float.class))
			return Float.class;
		else if (type.equals(int.class))
			return Integer.class;
		else if (type.equals(long.class))
			return Long.class;
		else if (type.equals(short.class))
			return Short.class;
		else if (type.equals(char.class))
			return Character.class;
		else if (type.equals(byte.class))
			return Byte.class;
		else
			return type;
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param type2
	 * 
	 * @return
	 */
	public static boolean classesEquals(Class<?> type1, Class<?> type2) {
		if (type1.equals(type2))
			return true;
		else if (CompareUtils.equalsAny(type1, booleanTypes))
			return CompareUtils.equalsAny(type2, booleanTypes);
		else if (CompareUtils.equalsAny(type1, doubleTypes))
			return CompareUtils.equalsAny(type2, doubleTypes);
		else if (CompareUtils.equalsAny(type1, floatTypes))
			return CompareUtils.equalsAny(type2, floatTypes);
		else if (CompareUtils.equalsAny(type1, integerTypes))
			return CompareUtils.equalsAny(type2, integerTypes);
		else if (CompareUtils.equalsAny(type1, longTypes))
			return CompareUtils.equalsAny(type2, longTypes);
		else if (CompareUtils.equalsAny(type1, shortTypes))
			return CompareUtils.equalsAny(type2, shortTypes);
		else if (CompareUtils.equalsAny(type1, charTypes))
			return CompareUtils.equalsAny(type2, charTypes);
		else if (CompareUtils.equalsAny(type1, byteTypes))
			return CompareUtils.equalsAny(type2, byteTypes);
		else
			return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param type2
	 * 
	 * @return
	 */
	public static boolean isAssignable(Class<?> type1, Class<?> type2) {
		return mapToNonPrimitive(type1).isAssignableFrom(mapToNonPrimitive(type2));
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param type2
	 * 
	 * @return
	 */
	public static boolean isCastable(Class<?> type1, Class<?> type2) {
		if (isCharType(type1))
			return isCharType(type2)
					|| isIntegerType(type2)
					|| isShortType(type2);
		else if (isIntegerType(type2))
			return isCharType(type2)
					|| isIntegerType(type2)
					|| isShortType(type2);
		else if (isShortType(type1))
			return isCharType(type2)
					|| isIntegerType(type2)
					|| isShortType(type2);
		else if (isLongType(type1))
			return isCharType(type2)
					|| isIntegerType(type2)
					|| isLongType(type2)
					|| isShortType(type2);
		else
			return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param type2
	 * 
	 * @return
	 */
	public static boolean isCastOrAssignable(Class<?> type1, Class<?> type2) {
		return isCastable(type1, type2) || mapToNonPrimitive(type1).isAssignableFrom(mapToNonPrimitive(type2));
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isPrimitiveType(Class<?> type) {
		return isBooleanType(type)
				|| isByteType(type)
				|| isCharType(type)
				|| isDoubleType(type)
				|| isFloatType(type)
				|| isIntegerType(type)
				|| isLongType(type)
				|| isShortType(type);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isBasicType(Class<?> type) {
		return isBooleanType(type)
				|| isDoubleType(type)
				|| isFloatType(type)
				|| isIntegerType(type)
				|| isLongType(type)
				|| isShortType(type)
				|| isCharType(type)
				|| isByteType(type)
				|| isStringType(type);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isBasicNumberType(Class<?> type) {
		return isDoubleType(type)
				|| isFloatType(type)
				|| isIntegerType(type)
				|| isLongType(type)
				|| isShortType(type)
				|| isCharType(type);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isDoubleType(Class<?> type) {
		return CompareUtils.equalsAny(type, doubleTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isFloatType(Class<?> type) {
		return CompareUtils.equalsAny(type, floatTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isIntegerType(Class<?> type) {
		return CompareUtils.equalsAny(type, integerTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isLongType(Class<?> type) {
		return CompareUtils.equalsAny(type, longTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isShortType(Class<?> type) {
		return CompareUtils.equalsAny(type, shortTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isBooleanType(Class<?> type) {
		return CompareUtils.equalsAny(type, booleanTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isCharType(Class<?> type) {
		return CompareUtils.equalsAny(type, charTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isByteType(Class<?> type) {
		return CompareUtils.equalsAny(type, byteTypes);
	}

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static boolean isStringType(Class<?> type) {
		return type.equals(String.class);
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param type2
	 * 
	 * @return
	 */
	public static Class<?> getMostCommonType(Class<?> type1, Class<?> type2) {
		if (type1.equals(Object.class) || type2.equals(Object.class))
			return Object.class;
		else if (type1.equals(type2))
			return type1;

		Class<?> currentType = type1;
		while (currentType != null && !currentType.equals(Object.class)) {
			if (currentType.isAssignableFrom(type2))
				return currentType;
			else
				currentType = currentType.getSuperclass();
		}

		currentType = type2;
		while (currentType != null && !currentType.equals(Object.class)) {
			if (currentType.isAssignableFrom(type1))
				return currentType;
			else
				currentType = currentType.getSuperclass();
		}

		return Object.class;
	}

	/**
	 * COMMENT
	 * 
	 * @param type1
	 * @param class2
	 * 
	 * @return
	 */
	public static Class<?> getMostCommonTypeVoidExcluded(Class<?> type1, Class<?> type2) {
		if (type1.equals(Void.class))
			return type2;
		else if (type2.equals(Void.class))
			return type1;
		else
			return getMostCommonType(type1, type2);
	}
}
