package de.uni_bremen.agra.fomeja.preprocessing.misc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import de.uni_bremen.agra.fomeja.decompiling.expressions.Expression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.BoolExpression;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.CompareExpr;
import de.uni_bremen.agra.fomeja.decompiling.expressions.bool.ConnectedBoolExpr;
import de.uni_bremen.agra.fomeja.types.BooleanConnector;
import de.uni_bremen.agra.fomeja.types.CompareOperator;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class CharSeqMap implements Cloneable {
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
	 * @param underlyingMap COMMENT
	 */
	public CharSeqMap(CharSeqMap underlyingMap) {
		this.charSeqMap = new HashMap<String, CharSeq>();
		this.substringExprs = new ArrayList<SubstringExpr>();
		this.subsequentExprs = new ArrayList<BoolExpression>();
		this.underlyingMap = underlyingMap;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public String getName() {
		return "string-CharSeqMap@" + Integer.toHexString(this.hashCode());
	}

	/* map methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * 
	 * @return COMMENT
	 */
	public CharSeq get(String name) {
		return this.charSeqMap.get(name) == null && this.underlyingMap != null ? this.underlyingMap.get(name) : this.charSeqMap.get(name);
	}

	/**
	 * COMMENT
	 * 
	 * @param atomStringExpr COMMENT
	 * 
	 * @return COMMENT
	 */
	public CharSeq getOrCreate(AtomStringExpr atomStringExpr) {
		CharSeq charSeq = this.get(atomStringExpr.getName());
		if (charSeq == null) {
			charSeq = new CharSeq(atomStringExpr);
			this.put(atomStringExpr.getName(), charSeq);
		}

		return charSeq;
	}

	/* substring connection methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param origCharSeq COMMENT
	 * @param substCharSeq COMMENT
	 * @param beginIdx COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean addSubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx) {
		return this.substringExprs.add(new SubstringExpr(origCharSeq, substCharSeq, beginIdx, -1));
	}

	/**
	 * COMMENT
	 * 
	 * @param origCharSeq COMMENT
	 * @param substCharSeq COMMENT
	 * @param beginIdx COMMENT
	 * @param endIdx COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean addSubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx, int endIdx) {
		return this.substringExprs.add(new SubstringExpr(origCharSeq, substCharSeq, beginIdx, endIdx));
	}

	/* subsequent CharSeq methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param stringExpr COMMENT
	 * @param operator COMMENT
	 * @param lengthValue COMMENT
	 */
	public void addSubsequentLengthValue(AtomStringExpr stringExpr, CompareOperator operator, Expression lengthValue) {
		this.subsequentExprs.add(new CompareExpr(stringExpr.getLengthExpr(), operator, lengthValue));
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeqMap COMMENT
	 */
	public void addAllSubsequentCharSeqs(CharSeqMap charSeqMap) {
		for (BoolExpression subsequentExpr : charSeqMap.subsequentExprs)
			this.subsequentExprs.add(subsequentExpr.clone());
	}

	/* CharSeq methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param charSeqName COMMENT
	 * @param operator COMMENT
	 * @param value COMMENT
	 */
	public void addLengthValue(String charSeqName, CompareOperator operator, int value) {
		if (this.wouldChangeLengthExpr(charSeqName, operator, value) && this.cloningGet(charSeqName) != null)
			this.get(charSeqName).addLengthValue(operator, value);
	}

	/**
	 * COMMENT
	 * 
	 * @param stringExpr COMMENT
	 * @param operator COMMENT
	 * @param value COMMENT
	 */
	public void addLengthValue(AtomStringExpr stringExpr, CompareOperator operator, int value) {
		if (this.wouldChangeLengthExpr(stringExpr.getName(), operator, value))
			this.cloningGetOrCreate(stringExpr).addLengthValue(operator, value);
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeqMap COMMENT
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
	 * @return COMMENT
	 */
	public ConnectedBoolExpr getCharSeqExprs() {
		return new ConnectedBoolExpr(BooleanConnector.AND, this.getLengthExpr(), this.getSubstringExpr(), this.getSubsequentExpr());
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
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
	 * @return COMMENT
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
	 * @return COMMENT
	 */
	public ConnectedBoolExpr getSubsequentExpr() {
		return new ConnectedBoolExpr(BooleanConnector.AND, this.subsequentExprs);
	}

	/* private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * @param charSeq COMMENT
	 * 
	 * @return COMMENT
	 */
	private CharSeq put(String name, CharSeq charSeq) {
		return this.charSeqMap.put(name, charSeq);
	}

	/**
	 * COMMENT
	 * 
	 * @param name COMMENT
	 * 
	 * @return COMMENT
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
	 * @param atomStringExpr COMMENT
	 * 
	 * @return COMMENT
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
	 * @param name COMMENT
	 * @param operator COMMENT
	 * @param value COMMENT
	 * 
	 * @return COMMENT
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

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
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
	 * @return COMMENT
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

	/* inner classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private static class SubstringExpr implements Cloneable {
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
		 * @param origcharSeq COMMENT
		 * @param substCharSeq COMMENT
		 * @param beginIdx COMMENT
		 * @param endIdx COMMENT
		 */
		public SubstringExpr(CharSeq origCharSeq, CharSeq substCharSeq, int beginIdx, int endIdx) {
			this.origCharSeq = origCharSeq;
			this.substCharSeq = substCharSeq;
			this.beginIdx = beginIdx;
			this.endIdx = endIdx;
		}

		/* getter/setter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public CharSeq getOrigCharSeq() {
			return this.origCharSeq;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public CharSeq getSubstCharSeq() {
			return this.substCharSeq;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public int getBeginIdx() {
			return this.beginIdx;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public int getEndIdx() {
			return this.endIdx < 0 || this.endIdx >= this.origCharSeq.maxLength() ? this.origCharSeq.maxLength() : this.endIdx-1;
		}

		/* class methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public ConnectedBoolExpr getExpr() {
			ConnectedBoolExpr connectedBoolExpr = new ConnectedBoolExpr(BooleanConnector.AND);
			for (int i=0; i<this.getEndIdx()-this.getBeginIdx()+1; i++)
				connectedBoolExpr.add(new CompareExpr(this.getSubstCharSeq().get(i), CompareOperator.EQUAL, this.getOrigCharSeq().get(i+this.getBeginIdx())));
			return connectedBoolExpr;
		}

		/* overridden methods
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
		public int hashCode() {
			return new HashCodeBuilder(101, 73)
					.append(this.origCharSeq)
					.append(this.substCharSeq)
					.toHashCode();
		}

		@Override
		public SubstringExpr clone() {
			return new SubstringExpr(this.origCharSeq, this.substCharSeq, this.beginIdx, this.endIdx);
		}
	}
}
