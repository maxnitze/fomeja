package de.uni_bremen.agra.fomeja.utils.constraintmethods;

/* imports */
import de.uni_bremen.agra.fomeja.annotations.PreparableMethod;
import de.uni_bremen.agra.fomeja.utils.StringUtils;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class StringMethods {
	/**
	 * COMMENT
	 */
	private StringMethods() {}

	/* encoding methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param character COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean isASCII(char character) {
		return character < StringUtils.MAX_ASCII;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean allCharsASCII(String string) {
		for (char c : string.toCharArray())
			if (c >= StringUtils.MAX_ASCII)
				return false;
		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean anyCharASCII(String string) {
		for (char c : string.toCharArray())
			if (c < StringUtils.MAX_ASCII)
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param character COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean isUTF8(char character) {
		return character < StringUtils.MAX_UTF8;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean allCharsUTF8(String string) {
		for (char c : string.toCharArray())
			if (c >= StringUtils.MAX_UTF8)
				return false;
		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean anyCharUTF8(String string) {
		for (char c : string.toCharArray())
			if (c < StringUtils.MAX_UTF8)
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param character COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean isUTF16(char character) {
		return character < StringUtils.MAX_UTF16;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean allCharsUTF16(String string) {
		for (char c : string.toCharArray())
			if (c >= StringUtils.MAX_UTF16)
				return false;
		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean anyCharUTF16(String string) {
		for (char c : string.toCharArray())
			if (c < StringUtils.MAX_UTF16)
				return true;
		return false;
	}

	/* hasChar methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param character COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasChar(String string, int character) {
		for (char c : string.toCharArray())
			if (c == character)
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param character COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasChar(String string, char character) {
		return hasChar(string, (int) character);
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAllChars(String string, int[] characters) {
		for (int c : characters)
			if (!hasChar(string, c))
				return false;
		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAllChars(String string, char[] characters) {
		for (char c : characters)
			if (!hasChar(string, c))
				return false;
		return true;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAllChars(String string, String characters) {
		return hasAllChars(string, characters.toCharArray());
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAnyChar(String string, int[] characters) {
		for (int c : characters)
			if (hasChar(string, c))
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAnyChar(String string, char[] characters) {
		for (char c : characters)
			if (hasChar(string, c))
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @param string COMMENT
	 * @param characters COMMENT
	 * 
	 * @return COMMENT
	 */
	@PreparableMethod
	public static boolean hasAnyChar(String string, String characters) {
		return hasAnyChar(string, characters.toCharArray());
	}
}
