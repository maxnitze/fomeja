package de.agra.sat.koselleck.utils;

/** imports */
import java.util.List;

/**
 * 
 * @author Max Nitze
 */
public abstract class StringUtils {
	/**
	 * 
	 * @param text
	 * @param regexes
	 * 
	 * @return
	 */
	public static boolean matchesAny(String text, List<String> regexes) {
		for(String regex : regexes)
			if(text.matches(regex))
				return true;
		return false;
	}
}
