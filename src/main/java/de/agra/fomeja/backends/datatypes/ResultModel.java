package de.agra.fomeja.backends.datatypes;

/* imports */
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.agra.fomeja.FomejaDefaults;

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
	 * @param key
	 * 
	 * @return
	 */
	public Object get(String key) {
		return this.results.get(key);
	}

	/**
	 * COMMENT
	 * 
	 * @param key
	 * @param type
	 * 
	 * @return
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
	 * @param key
	 * @param value
	 * 
	 * @return
	 */
	public Object put(String key, Object value) {
		return this.results.put(key, value);
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Set<Map.Entry<String, Object>> entrySet() {
		return this.results.entrySet();
	}
}
