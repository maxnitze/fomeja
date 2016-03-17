package de.uni_bremen.agra.fomeja.decompiling.statements.misc;

/* imports */
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class State {
	/** COMMENT */
	private Map<String, Expression> exprs;

	/**
	 * COMMENT
	 */
	public State() {
		this.exprs = new HashMap<String, Expression>();
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Map<String, Expression> getExprs() {
		return this.exprs;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param key
	 * @param value
	 */
	public void put(String key, Expression value) {
		this.exprs.put(key, value);
		this.substitude(this.exprs);
	}

	/**
	 * COMMENT
	 * 
	 * @param exprs
	 */
	public void putAll(Map<String, Expression> exprs) {
		this.exprs.putAll(exprs);
		this.substitude(this.exprs);
	}

	/**
	 * COMMENT
	 * 
	 * @param key
	 * 
	 * @return
	 */
	public Expression get(String key) {
		return this.exprs.get(key);
	}

	/**
	 * COMMENT
	 * 
	 * @param key
	 * 
	 * @return
	 */
	public boolean contains(String key) {
		return this.exprs.containsKey(key);
	}

	/**
	 * COMMENT
	 * 
	 * @param substExprs
	 */
	public void substitude(Map<String, Expression> substExprs) {
		Map<String, Expression> exprs = new HashMap<String, Expression>();
		for (Entry<String, Expression> entry : this.exprs.entrySet())
			exprs.put(entry.getKey(), entry.getValue().clone().substitude(substExprs));
		this.exprs = exprs;
	}

	/**
	 * COMMENT
	 * 
	 * @param state
	 */
	public void merge(State state) {
		for (Entry<String, Expression> entry : state.getExprs().entrySet())
			if (this.get(entry.getKey()) != null)
				this.put(entry.getKey(), entry.getValue());
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public State clone() {
		State state = new State();
		state.exprs.putAll(this.exprs);
		return state;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public String toString() {
		StringBuilder stateString = new StringBuilder();
		for (Entry<String, Expression> expr : this.exprs.entrySet()) {
			if (stateString.length() > 0)
				stateString.append("\n");
			stateString.append(expr.getKey());
			stateString.append(" = ");
			stateString.append(expr.getValue().toString());
		}
		return stateString.toString();
	}
}
