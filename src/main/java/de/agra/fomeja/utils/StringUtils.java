package de.agra.fomeja.utils;

/** imports */
import java.util.List;

/**
 * StringUtils provides functions for strings.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public final class StringUtils {
	/** COMMENT */
	public static final int MAX_ASCII = 1 << 7;
	/** COMMENT */
	public static final int MAX_UTF8 = 1 << 8;
	/** COMMENT */
	public static final int MAX_UTF16 = 1 << 16;

	/**
	 * Private Constructor to prevent this class from being instantiated.
	 */
	private StringUtils() {}

	/**
	 * matchesAny checks if any of regular expressions of the given array
	 *  matches the given text.
	 * 
	 * @param text the text
	 * @param regexes the array of regular expressions
	 * 
	 * @return {@code true} if any of the regular expressions of the array
	 *  matches the given text, {@code false} otherwise
	 */
	public static boolean matchesAny(String text, String[] regexes) {
		for (String regex : regexes)
			if (text.matches(regex))
				return true;
		return false;
	}

	/**
	 * matchesAny checks if any of regular expressions of the given list
	 *  matches the given text.
	 * 
	 * @param text the text
	 * @param regexes the list of regular expressions
	 * 
	 * @return {@code true} if any of the regular expressions of the list
	 *  matches the given text, {@code false} otherwise
	 */
	public static boolean matchesAny(String text, List<String> regexes) {
		for (String regex : regexes)
			if (text.matches(regex))
				return true;
		return false;
	}
}
