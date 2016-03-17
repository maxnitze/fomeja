package de.uni_bremen.agra.fomeja.backends.datatypes;

/* imports */
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_bremen.agra.fomeja.FomejaDefaults;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ResultModel {
	/** COMMENT */
	private Map<String, Object> results;

	/**
	 * COMMENT
	 */
	public ResultModel() {
		this.results = new HashMap<String, Object>();
	}

	/**
	 * COMMENT
	 * 
	 * @param key COMMENT
	 * 
	 * @return COMMENT
	 */
	public Object get(String key) {
		return this.results.get(key);
	}

	/**
	 * COMMENT
	 * 
	 * @param key COMMENT
	 * @param type COMMENT
	 * 
	 * @return COMMENT
	 */
	public Object getOrDefault(String key, Class<?> type) {
		Object result = this.results.get(key);
		if (result == null)
			result = FomejaDefaults.getDefaultForPrimitiveType(type);
		return result;
	}

	/**
	 * COMMENT
	 * 
	 * @param key COMMENT
	 * @param value COMMENT
	 * 
	 * @return COMMENT
	 */
	public Object put(String key, Object value) {
		return this.results.put(key, value);
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public Set<Map.Entry<String, Object>> entrySet() {
		return this.results.entrySet();
	}
}
