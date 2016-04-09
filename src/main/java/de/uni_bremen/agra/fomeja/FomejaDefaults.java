package de.uni_bremen.agra.fomeja;

/* imports */
import de.uni_bremen.agra.fomeja.backends.Prover;
import de.uni_bremen.agra.fomeja.backends.Z3SMTIIJava;
import de.uni_bremen.agra.fomeja.utils.ClassUtils;

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

	/** COMMENT */
	private boolean validateModelObjectsByDefault;

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

		this.validateModelObjectsByDefault = true;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static FomejaDefaults getSingleton() {
		if (singleton == null)
			singleton = new FomejaDefaults();
		return singleton;
	}

	/* static getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static boolean getDefaultBooleanValue() {
		return getSingleton().defaultBooleanValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultBooleanValue COMMENT
	 */
	public static void setDefaultBooleanValue(boolean defaultBooleanValue) {
		getSingleton().defaultBooleanValue = defaultBooleanValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static byte getDefaultByteValue() {
		return getSingleton().defaultByteValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultByteValue COMMENT
	 */
	public static void setDefaultByteValue(byte defaultByteValue) {
		getSingleton().defaultByteValue = defaultByteValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static char getDefaultCharValue() {
		return getSingleton().defaultCharValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultCharValue COMMENT
	 */
	public static void setDefaultCharValue(char defaultCharValue) {
		getSingleton().defaultCharValue = defaultCharValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static double getDefaultDoubleValue() {
		return getSingleton().defaultDoubleValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultDoubleValue COMMENT
	 */
	public static void setDefaultDoubleValue(double defaultDoubleValue) {
		getSingleton().defaultDoubleValue = defaultDoubleValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static float getDefaultFloatValue() {
		return getSingleton().defaultFloatValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultFloatValue COMMENT
	 */
	public static void setDefaultFloatValue(float defaultFloatValue) {
		getSingleton().defaultFloatValue = defaultFloatValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static int getDefaultIntegerValue() {
		return getSingleton().defaultIntegerValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultIntegerValue COMMENT
	 */
	public static void setDefaultIntegerValue(int defaultIntegerValue) {
		getSingleton().defaultIntegerValue = defaultIntegerValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static long getDefaultLongValue() {
		return getSingleton().defaultLongValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultLongValue COMMENT
	 */
	public static void setDefaultLongValue(long defaultLongValue) {
		getSingleton().defaultLongValue = defaultLongValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static short getDefaultShortValue() {
		return getSingleton().defaultShortValue;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultShortValue COMMENT
	 */
	public static void setDefaultShortValue(short defaultShortValue) {
		getSingleton().defaultShortValue = defaultShortValue;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static int getDefaultEnumOrdinal() {
		return getSingleton().defaultEnumOrdinal;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultEnumOrdinal COMMENT
	 */
	public static void setDefaultEnumOrdinal(int defaultEnumOrdinal) {
		getSingleton().defaultEnumOrdinal = defaultEnumOrdinal;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static int getDefaultStringLength() {
		return getSingleton().defaultStringLength;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultStringLength COMMENT
	 */
	public static void setDefaultStringLength(int defaultStringLength) {
		getSingleton().defaultStringLength = defaultStringLength;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static Prover<?> getDefaultProver() {
		return getSingleton().defaultProver;
	}

	/**
	 * COMMENT
	 * 
	 * @param defaultProver COMMENT
	 */
	public static void setDefaultProver(Prover<?> defaultProver) {
		getSingleton().defaultProver = defaultProver;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public static boolean validateModelObjectsByDefault() {
		return getSingleton().validateModelObjectsByDefault;
	}

	/**
	 * COMMENT
	 * 
	 * @param validateModelObjectsByDefault COMMENT
	 */
	public static void validateModelObjectsByDefault(boolean validateModelObjectsByDefault) {
		getSingleton().validateModelObjectsByDefault = validateModelObjectsByDefault;
	}

	/* public methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param type COMMENT
	 * 
	 * @return COMMENT
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
