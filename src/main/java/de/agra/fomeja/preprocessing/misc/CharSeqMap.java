package de.agra.fomeja.preprocessing.misc;

/* imports */
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.agra.fomeja.decompiling.expressions.Expression;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.agra.fomeja.types.BooleanConnector;
import de.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class CharSeqMap {
	/** COMMENT */
	private Map<String, CharSeq> charSeqMap;
	/** COMMENT */
	private List<SubstringExpr> substringExprs;
	/** COMMENT */
	private List<BoolExpression> subsequentExprs;

	/** COMMENT */
	private CharSeqMap underlyingMap;

	/**
	 * COMMENT
	 */
	public CharSeqMap() {
		this(null);
	}

	/**
	 * COMMENT
	 * 
	 * @param underlyingMap
	 */
	public CharSeqMap(CharSeqMap underlyingMap) {
		this.charSeqMap = new HashMap<String, CharSeq>();
		this.substringExprs = new ArrayList<SubstringExpr>();
		this.subsequentExprs = new ArrayList<BoolExpression>();
		this.underlyingMap = underlyingMap;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return "string-CharSeqMap@" + Integer.toHexString(this.hashCode());
	}

	/** map methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name
	 * 
	 * @return
	 */
	public CharSeq get(String name) {
		return this.charSeqMap.get(name) == null && this.underlyingMap != null ? this.underlyingMap.get(name) : this.charSeqMap.get(name);
	}

	/**
	 * COMMENT
	 * 
	 * @param atomStringExpr
	 * 
	 * @return
	 */
	public CharSeq getOrCreate(AtomStringExpr atomStringExpr) {
		CharSeq charSeq = this.get(atomStringExpr.getName());
		if (charSeq == null) {
			charSeq = new CharSeq(atomStringExpr);
			this.put(atomStringExpr.getName(), charSeq);
		}

		return charSeq;
	}

	/** substring connection methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param origCharSeq
	 * @param substCharSeq
	 * @param beginIdx
	 * 
	 * @return
	 */
	public boolean addSubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx) {
		return this.substringExprs.add(new SubstringExpr(origCharSeq, substCharSeq, beginIdx, -1));
	}

	/**
	 * COMMENT
	 * 
	 * @param origCharSeq
	 * @param substCharSeq
	 * @param beginIdx
	 * @param endIdx
	 * 
	 * @return
	 */
	public boolean addSubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx, int endIdx) {
		return this.substringExprs.add(new SubstringExpr(origCharSeq, substCharSeq, beginIdx, endIdx));
	}

	/** subsequent CharSeq methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param stringExpr
	 * @param operator
	 * @param lengthValue
	 */
	public void addSubsequentLengthValue(AtomStringExpr stringExpr, CompareOperator operator, Expression lengthValue) {
		this.subsequentExprs.add(new CompareExpr(stringExpr.getLengthExpr(), operator, lengthValue));
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeqMap
	 */
	public void addAllSubsequentCharSeqs(CharSeqMap charSeqMap) {
		for (BoolExpression subsequentExpr : charSeqMap.subsequentExprs)
			this.subsequentExprs.add(subsequentExpr.clone());
	}

	/** CharSeq methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param charSeqName
	 * @param operator
	 * @param value
	 */
	public void addLengthValue(String charSeqName, CompareOperator operator, int value) {
		if (this.wouldChangeLengthExpr(charSeqName, operator, value) && this.cloningGet(charSeqName) != null)
			this.get(charSeqName).addLengthValue(operator, value);
	}

	/**
	 * COMMENT
	 * 
	 * @param stringExpr
	 * @param operator
	 * @param value
	 */
	public void addLengthValue(AtomStringExpr stringExpr, CompareOperator operator, int value) {
		if (this.wouldChangeLengthExpr(stringExpr.getName(), operator, value))
			this.cloningGetOrCreate(stringExpr).addLengthValue(operator, value);
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeqMap
	 */
	public void merge(CharSeqMap charSeqMap) {
		for (Map.Entry<String, CharSeq> charSeqMapEntry : charSeqMap.charSeqMap.entrySet()) {
			CharSeq charSeq = this.charSeqMap.get(charSeqMapEntry.getKey());
			if (charSeq == null) {
				charSeq = charSeqMapEntry.getValue().clone();
				this.charSeqMap.put(charSeqMapEntry.getKey(), charSeq);
			} else
				charSeq.addLengthValues(charSeqMapEntry.getValue());
		}
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ConnectedBoolExpr getCharSeqExprs() {
		return new ConnectedBoolExpr(BooleanConnector.AND, this.getLengthExpr(), this.getSubstringExpr(), this.getSubsequentExpr());
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ConnectedBoolExpr getLengthExpr() {
		ConnectedBoolExpr lengthExpr = new ConnectedBoolExpr(BooleanConnector.AND);
		for (Map.Entry<String, CharSeq> charSeqMapEntry : this.charSeqMap.entrySet())
			if (charSeqMapEntry.getValue().isVariable())
				lengthExpr.add(charSeqMapEntry.getValue().getLengthExpr());
		return lengthExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ConnectedBoolExpr getSubstringExpr() {
		ConnectedBoolExpr connectedBoolExpr = new ConnectedBoolExpr(BooleanConnector.AND);
		for (SubstringExpr substringExpr : this.substringExprs)
			connectedBoolExpr.add(substringExpr.getExpr());
			
		return connectedBoolExpr;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ConnectedBoolExpr getSubsequentExpr() {
		return new ConnectedBoolExpr(BooleanConnector.AND, this.subsequentExprs);
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param charSeq
	 * 
	 * @return
	 */
	private CharSeq put(String name, CharSeq charSeq) {
		return this.charSeqMap.put(name, charSeq);
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * 
	 * @return
	 */
	private CharSeq cloningGet(String name) {
		CharSeq charSeq = this.charSeqMap.get(name);
		if (charSeq == null && this.underlyingMap != null) {
			charSeq = this.underlyingMap.get(name);
			if (charSeq != null) {
				charSeq = charSeq.clone();
				this.put(charSeq.getName(), charSeq);
			}
		} else if (charSeq != null)
			charSeq = charSeq.clone();

		return charSeq;
	}

	/**
	 * COMMENT
	 * 
	 * @param atomStringExpr
	 * 
	 * @return
	 */
	public CharSeq cloningGetOrCreate(AtomStringExpr atomStringExpr) {
		CharSeq charSeq = this.cloningGet(atomStringExpr.getName());
		if (charSeq == null) {
			charSeq = new CharSeq(atomStringExpr);
			this.put(charSeq.getName(), charSeq);
		}

		return charSeq;
	}

	/**
	 * COMMENT
	 * 
	 * @param name
	 * @param operator
	 * @param value
	 * 
	 * @return
	 */
	private boolean wouldChangeLengthExpr(String name, CompareOperator operator, int value) {
		CharSeq charSeq = this.get(name);
		if (charSeq == null)
			return true;

		switch (operator) {
		case EQUAL:
			return value > charSeq.minLength() || value < charSeq.maxLength();
		case GREATER:
			return value >= charSeq.minLength();
		case GREATER_EQUAL:
			return value > charSeq.minLength();
		case LESS:
			return value <= charSeq.maxLength();
		case LESS_EQUAL:
			return value < charSeq.maxLength();
		default:
			return false;
		}
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public CharSeqMap clone() {
		CharSeqMap clonedCharSeqMap = new CharSeqMap(this.underlyingMap);
		for (Map.Entry<String, CharSeq> mapEntry : this.charSeqMap.entrySet())
			clonedCharSeqMap.charSeqMap.put(mapEntry.getKey(), mapEntry.getValue().clone());

		for (SubstringExpr substringExpr : this.substringExprs)
			clonedCharSeqMap.substringExprs.add(substringExpr.clone());

		for (BoolExpression subsequentExpr : this.subsequentExprs)
			clonedCharSeqMap.subsequentExprs.add(subsequentExpr.clone());

		return clonedCharSeqMap;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder(this.getName());
		for (Map.Entry<String, CharSeq> entry : this.charSeqMap.entrySet())
			stringBuilder
					.append("\n  ")
					.append(entry.getKey())
					.append(": ")
					.append(entry.getValue().toString());
		return stringBuilder.toString();
	}

	/** inner classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private class SubstringExpr {
		/** COMMENT */
		private CharSeq origCharSeq;
		/** COMMENT */
		private CharSeq substCharSeq;
		/** COMMENT */
		private int beginIdx;
		/** COMMENT */
		private int endIdx;

		/**
		 * COMMENT
		 * 
		 * @param origcharSeq
		 * @param substCharSeq
		 * @param beginIdx
		 * @param endIdx
		 */
		public SubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx, int endIdx) {
			this.origCharSeq = origCharSeq;
			this.substCharSeq = substCharSeq;
			this.beginIdx = beginIdx;
			this.endIdx = endIdx;
		}

		/** getter/setter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public CharSeq getOrigCharSeq() {
			return this.origCharSeq;
		}

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public CharSeq getSubstCharSeq() {
			return this.substCharSeq;
		}

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public int getBeginIdx() {
			return this.beginIdx;
		}

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public int getEndIdx() {
			return this.endIdx < 0 || this.endIdx >= this.origCharSeq.maxLength() ? this.origCharSeq.maxLength() : this.endIdx-1;
		}

		/** class methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return
		 */
		public ConnectedBoolExpr getExpr() {
			ConnectedBoolExpr connectedBoolExpr = new ConnectedBoolExpr(BooleanConnector.AND);
			for (int i=0; i<this.getEndIdx()-this.getBeginIdx()+1; i++)
				connectedBoolExpr.add(new CompareExpr(this.getSubstCharSeq().get(i), CompareOperator.EQUAL, this.getOrigCharSeq().get(i+this.getBeginIdx())));
			return connectedBoolExpr;
		}

		/** overridden methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public boolean equals(Object object) {
			if (!(object instanceof SubstringExpr))
				return false;

			SubstringExpr substringConnection = (SubstringExpr) object;

			return this.origCharSeq == substringConnection.origCharSeq
					&& this.substCharSeq == substringConnection.substCharSeq;
		}

		@Override
		public SubstringExpr clone() {
			return new SubstringExpr(this.origCharSeq, this.substCharSeq, this.beginIdx, this.endIdx);
		}
	}
}
