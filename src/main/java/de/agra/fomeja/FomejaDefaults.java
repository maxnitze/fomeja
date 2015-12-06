package de.agra.fomeja;

/* imports */
import de.agra.fomeja.backends.Prover;
import de.agra.fomeja.backends.Z3SMTIIJava;
import de.agra.fomeja.utils.ClassUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class FomejaDefaults {
	/** COMMENT */
	private static FomejaDefaults singleton;

	/** COMMENT */
	private boolean defaultBooleanValue;
	/** COMMENT */
	private byte defaultByteValue;
	/** COMMENT */
	private char defaultCharValue;
	/** COMMENT */
	private double defaultDoubleValue;
	/** COMMENT */
	private float defaultFloatValue;
	/** COMMENT */
	private int defaultIntegerValue;
	/** COMMENT */
	private long defaultLongValue;
	/** COMMENT */
	private short defaultShortValue;

	/** COMMENT */
	private int defaultEnumOrdinal;

	/** COMMENT */
	private int defaultStringLength;

	/** COMMENT */
	private Prover<?> defaultProver;

	/**
	 * Private constructor to prevent this class from being instantiated
	 */
	private FomejaDefaults() {
		this.defaultBooleanValue = false;
		this.defaultByteValue = 0;
		this.defaultCharValue = '\0';
		this.defaultDoubleValue = 0d;
		this.defaultFloatValue = 0f;
		this.defaultIntegerValue = 0;
		this.defaultLongValue = 0l;
		this.defaultShortValue = 0;

		this.defaultEnumOrdinal = 0;

		this.defaultStringLength = 256;

		this.defaultProver = new Z3SMTIIJava();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static FomejaDefaults getSingleton() {
		if (singleton == null)
			singleton = new FomejaDefaults();
		return singleton;
	}

	/** static getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static boolean getDefaultBooleanValue() {
		return getSingleton().defaultBooleanValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultBooleanValue
	 */
	public static void setDefaultBooleanValue(boolean defaultBooleanValue) {
		getSingleton().defaultBooleanValue = defaultBooleanValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static byte getDefaultByteValue() {
		return getSingleton().defaultByteValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultByteValue
	 */
	public static void setDefaultByteValue(byte defaultByteValue) {
		getSingleton().defaultByteValue = defaultByteValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static char getDefaultCharValue() {
		return getSingleton().defaultCharValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultCharValue
	 */
	public static void setDefaultCharValue(char defaultCharValue) {
		getSingleton().defaultCharValue = defaultCharValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static double getDefaultDoubleValue() {
		return getSingleton().defaultDoubleValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultDoubleValue
	 */
	public static void setDefaultDoubleValue(double defaultDoubleValue) {
		getSingleton().defaultDoubleValue = defaultDoubleValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static float getDefaultFloatValue() {
		return getSingleton().defaultFloatValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultFloatValue
	 */
	public static void setDefaultFloatValue(float defaultFloatValue) {
		getSingleton().defaultFloatValue = defaultFloatValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static int getDefaultIntegerValue() {
		return getSingleton().defaultIntegerValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultIntegerValue
	 */
	public static void setDefaultIntegerValue(int defaultIntegerValue) {
		getSingleton().defaultIntegerValue = defaultIntegerValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static long getDefaultLongValue() {
		return getSingleton().defaultLongValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultLongValue
	 */
	public static void setDefaultLongValue(long defaultLongValue) {
		getSingleton().defaultLongValue = defaultLongValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static short getDefaultShortValue() {
		return getSingleton().defaultShortValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultShortValue
	 */
	public static void setDefaultShortValue(short defaultShortValue) {
		getSingleton().defaultShortValue = defaultShortValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static int getDefaultEnumOrdinal() {
		return getSingleton().defaultEnumOrdinal;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultEnumOrdinal
	 */
	public static void setDefaultEnumOrdinal(int defaultEnumOrdinal) {
		getSingleton().defaultEnumOrdinal = defaultEnumOrdinal;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static int getDefaultStringLength() {
		return getSingleton().defaultStringLength;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultStringLength
	 */
	public static void setDefaultStringLength(int defaultStringLength) {
		getSingleton().defaultStringLength = defaultStringLength;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public static Prover<?> getDefaultProver() {
		return getSingleton().defaultProver;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultProver
	 */
	public static void setDefaultProver(Prover<?> defaultProver) {
		getSingleton().defaultProver = defaultProver;
	}

	/** public methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param type
	 * 
	 * @return
	 */
	public static Object getDefaultForPrimitiveType(Class<?> type) {
		if (ClassUtils.isBooleanType(type))
			return getDefaultBooleanValue();
		else if (ClassUtils.isByteType(type))
			return getDefaultByteValue();
		else if (ClassUtils.isCharType(type))
			return getDefaultCharValue();
		else if (ClassUtils.isDoubleType(type))
			return getDefaultDoubleValue();
		else if (ClassUtils.isFloatType(type))
			return getDefaultFloatValue();
		else if (ClassUtils.isIntegerType(type))
			return getDefaultIntegerValue();
		else if (ClassUtils.isLongType(type))
			return getDefaultLongValue();
		else if (ClassUtils.isShortType(type))
			return getDefaultShortValue();
		else if (type.isEnum())
			return getDefaultEnumOrdinal();
		else
			return null;
	}
}
