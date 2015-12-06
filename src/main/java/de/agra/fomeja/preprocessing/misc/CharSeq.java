package de.agra.fomeja.preprocessing.misc;

/* imports */
import org.apache.log4j.Logger;

import de.agra.fomeja.FomejaDefaults;
import de.agra.fomeja.backends.SMTIIJava;
import de.agra.fomeja.decompiling.expressions.atomar.AtomCharacterExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomIntegerExpr;
import de.agra.fomeja.decompiling.expressions.atomar.AtomStringExpr;
import de.agra.fomeja.decompiling.expressions.bool.AtomBoolExpr;
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
public class CharSeq {
	/** COMMENT */
	private AtomStringExpr expr;
	/** COMMENT */
	private boolean isVariable;
	/** COMMENT */
	private AtomCharacterExpr[] charSeq;

	/** COMMENT */
	private int minLength;
	/** COMMENT */
	private int maxLength;
	/** COMMENT */
	private int curLength;
	/** COMMENT */
	private boolean maxLengthChanged;

	/**
	 * COMMENT
	 * 
	 * @param expr
	 */
	public CharSeq(AtomStringExpr expr) {
		this.expr = expr;
		this.isVariable = expr.isVariable() || expr.getPreFieldList().isVariable();

		if (this.isVariable) {
			this.charSeq = new AtomCharacterExpr[FomejaDefaults.getDefaultStringLength()+1];
			for (int i=0; i<=FomejaDefaults.getDefaultStringLength(); i++)
				this.charSeq[i] = expr.getCharacterExpr(i);

			this.minLength = 0;
			this.maxLength = Integer.MAX_VALUE;
			this.curLength = Integer.MAX_VALUE;
		} else {
			this.charSeq = new AtomCharacterExpr[expr.getValue().length()+1];
			for (int i=0; i<expr.getValue().length(); i++)
				this.charSeq[i] = new AtomCharacterExpr(expr.getValue().charAt(i));
			this.charSeq[expr.getValue().length()] = new AtomCharacterExpr('\0');

			this.minLength = expr.getValue().length();
			this.maxLength = expr.getValue().length();
			this.curLength = expr.getValue().length();
		}

		this.maxLengthChanged = false;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public AtomStringExpr getExpr() {
		return this.expr;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		return this.expr.getName();
	}

	/**
	 * COMMENT
	 * 
	 * @param index
	 * 
	 * @return
	 */
	public AtomCharacterExpr get(int index) {
		return this.charSeq[index];
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isVariable() {
		return this.isVariable;
	}

	/** length methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int minLength() {
		this.updateCharArray();
		return this.minLength;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int maxLength() {
		this.updateCharArray();
		return this.maxLength < Integer.MAX_VALUE ? this.maxLength : FomejaDefaults.getDefaultStringLength();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int curLength() {
		this.updateCharArray();
		return this.curLength < Integer.MAX_VALUE ? this.curLength : FomejaDefaults.getDefaultStringLength();
	}

	/**
	 * COMMENT
	 * 
	 * @param length
	 * 
	 * @return
	 */
	public int setCurLength(int length) {
		this.curLength = length;
		this.updateCurLength();
		return this.curLength;
	}

	/**
	 * COMMENT
	 * 
	 * @param operator
	 * @param value
	 */
	public void addLengthValue(CompareOperator operator, int value) {
		if (value >= 0 && value < Integer.MAX_VALUE) {
			int oldMaxLength = this.maxLength;

			if (operator == CompareOperator.EQUAL) {
				this.minLength = value > this.minLength ? value : this.minLength;
				this.maxLength = value < this.maxLength ? value : this.maxLength;
			} else if (operator == CompareOperator.GREATER_EQUAL)
				this.minLength = value > this.minLength ? value : this.minLength;
			else if (operator == CompareOperator.GREATER)
				this.minLength = value+1 > this.minLength ? value+1 : this.minLength;
			else if (operator == CompareOperator.LESS_EQUAL)
				this.maxLength = value < this.maxLength ? value : this.maxLength;
			else if (operator == CompareOperator.LESS)
				this.maxLength = value-1 < this.maxLength ? value-1 : this.maxLength;

			if (oldMaxLength != this.maxLength)
				this.maxLengthChanged = true;
			this.updateCurLength();
		} else {
			String message = "length value \"lv\" needs to be \"0\" <= \"lv\" < \"" + Integer.MAX_VALUE + "\"  but is \"" + value + "\"";
			Logger.getLogger(SMTIIJava.class).error(message);
			throw new IndexOutOfBoundsException(message);
		}
	}

	/**
	 * COMMENT
	 * 
	 * @param charSeq
	 */
	public void addLengthValues(CharSeq charSeq) {
		this.addLengthValue(CompareOperator.GREATER_EQUAL, charSeq.minLength());
		this.addLengthValue(CompareOperator.LESS_EQUAL, charSeq.maxLength());
	}

	/** expression methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public BoolExpression getLengthExpr() {
		if (this.minLength > this.maxLength)
			return new AtomBoolExpr(false);

		this.updateCharArray();

		ConnectedBoolExpr minExprs = new ConnectedBoolExpr(BooleanConnector.AND);
		ConnectedBoolExpr maxExprs = new ConnectedBoolExpr(BooleanConnector.OR);
		for (int i=0; i<this.maxLength()+1; i++) {
			if (i<this.minLength())
				minExprs.add(new CompareExpr(this.get(i), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(0)));
			else {
				ConnectedBoolExpr innerMaxExpr = new ConnectedBoolExpr(BooleanConnector.AND);
				for (int j=this.minLength(); j<i; j++)
					innerMaxExpr.add(new CompareExpr(this.get(j), CompareOperator.GREATER_EQUAL, new AtomIntegerExpr(0)));
				innerMaxExpr.add(new CompareExpr(this.get(i), CompareOperator.LESS, new AtomIntegerExpr(0)));
				innerMaxExpr.add(new CompareExpr(this.expr.getLengthExpr(), CompareOperator.EQUAL, new AtomIntegerExpr(i)));
				maxExprs.add(innerMaxExpr);
			}
		}

		minExprs.add(maxExprs);

		return minExprs;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public ConnectedBoolExpr getCharBoundaryExpr() {
		ConnectedBoolExpr charBoundaryExpr = new ConnectedBoolExpr(BooleanConnector.AND);
		for (int i=0; i<this.maxLength(); i++)
			charBoundaryExpr.add(this.getCharBoundaries(i));

		return charBoundaryExpr;
	}

	/** overridden methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public CharSeq clone() {
		CharSeq clonedCharSeq = new CharSeq(this.expr);
		clonedCharSeq.addLengthValue(CompareOperator.GREATER_EQUAL, this.minLength());
		clonedCharSeq.addLengthValue(CompareOperator.LESS_EQUAL, this.maxLength());

		clonedCharSeq.updateCharArray();

		return clonedCharSeq;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		if (this.isVariable) {
			stringBuilder
					.append(this.getName())
					.append(" variable with length between ")
					.append(this.minLength())
					.append(" and ")
					.append(this.maxLength());
		} else {
			stringBuilder
					.append("non-variable with length ")
					.append(this.maxLength())
					.append(": ");
			for (AtomCharacterExpr charExpr : this.charSeq)
				stringBuilder.append(charExpr.getValue());
		}

		return stringBuilder.toString();
	}

	/** private methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param i
	 * 
	 * @return
	 */
	private BoolExpression getCharBoundaries(int i) {
		return new CompareExpr(this.charSeq[i], CompareOperator.LESS, new AtomIntegerExpr(this.getUpperBoundary()));
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	private int getUpperBoundary() {
		return 1 << 16;
	}

	/**
	 * COMMENT
	 */
	private void updateCharArray() {
		if (this.isVariable && this.maxLengthChanged && this.maxLength != Integer.MAX_VALUE && this.maxLength > this.charSeq.length-1) {
			AtomCharacterExpr[] oldCharSeq = this.charSeq;
			this.charSeq = new AtomCharacterExpr[this.maxLength+1];
			for (int i=0; i<this.charSeq.length; i++) {
				if (i<oldCharSeq.length)
					this.charSeq[i] = oldCharSeq[i];
				else
					this.charSeq[i] = expr.getCharacterExpr(i);
			}

			this.maxLengthChanged = false;
		}
	}

	/**
	 * COMMENT
	 */
	private void updateCurLength() {
		if (this.curLength < this.minLength)
			this.curLength = this.minLength;

		if (this.curLength > this.maxLength)
			this.curLength = this.maxLength;
	}
}