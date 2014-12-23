package de.agra.sat.koselleck.datatypes;

/** imports */
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.agra.sat.koselleck.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PreFieldList extends LinkedList<PreField> {
	/** generated serialisation uid */
	private static final long serialVersionUID = -4686167580108058185L;

	/** COMMENT */
	private int fieldCodeIndex;
	/** COMMENT */
	private Opcode opcode;

	/** COMMENT */
	private int variablePreFields;

	/**
	 * COMMENT
	 * 
	 * @param fieldCodeIndex
	 * @param opcode
	 */
	public PreFieldList(int fieldCodeIndex, Opcode opcode) {
		this.fieldCodeIndex = fieldCodeIndex;
		this.opcode = opcode;
		this.variablePreFields = 0;
	}

	/**
	 * COMMENT
	 * 
	 * @param fieldCodeIndex
	 * @param opcode
	 * @param preFields
	 */
	public PreFieldList(int fieldCodeIndex, Opcode opcode, List<PreField> preFields) {
		super(preFields);
		this.fieldCodeIndex = fieldCodeIndex;
		this.opcode = opcode;
		this.variablePreFields = 0;
		for (PreField preField : preFields)
			if (preField.isVariable())
				++this.variablePreFields;
	}

	/* class methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public String getName() {
		String name = "v" + this.fieldCodeIndex;
		for (PreField preField : this)
			name += "_" + preField.getSubName();

		return name;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getFieldCodeIndex() {
		return this.fieldCodeIndex;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public Opcode getOpcode() {
		return this.opcode;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public boolean isVariable() {
		return this.variablePreFields > 0;
	}

	/**
	 * COMMENT
	 * 
	 * TODO remove when support for multiple variable fields is
	 *  implemented
	 * 
	 * @return
	 */
	public boolean isSingleVariable() {
		return this.variablePreFields == 1;
	}

	/**
	 * COMMENT
	 * 
	 * @param index
	 * 
	 * @return
	 */
	public PreFieldList head(int index) {
		return new PreFieldList(this.fieldCodeIndex, this.opcode, this.subList(0, index >= 0 ? index : this.size()+index));
	}

	/**
	 * COMMENT
	 * 
	 * @param index
	 * 
	 * @return
	 */
	public PreFieldList tail(int index) {
		return new PreFieldList(this.fieldCodeIndex, this.opcode, this.subList(index >= 0 ? index : this.size()-1+index, this.size()));
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreField first() {
		if (this.size() > 0)
			return this.get(0);
		else
			return null;
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public PreField last() {
		if (this.size() > 0)
			return this.get(this.size()-1);
		else
			return null;
	}

	/**
	 * COMMENT
	 * 
	 * @param preFieldList
	 * 
	 * @return
	 */
	public boolean isListPrefix(PreFieldList preFieldList) {
		if (this.size() < preFieldList.size())
			return false;
		for (int i=0; i<preFieldList.size() ; i++)
			if (!this.get(i).equals(preFieldList.get(i)))
				return false;
		return true;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean add(PreField preField) {
		boolean result = super.add(preField);
		if (result && preField.isVariable())
			++this.variablePreFields;
		return result;
	}

	@Override
	public boolean addAll(Collection<? extends PreField> preFields) {
		boolean result = false;
		for (PreField preField : preFields)
			result |= this.add(preField);
		return result;
	}

	@Override
	public boolean remove(Object object) {
		boolean result = this.remove(object);
		if (result && object instanceof PreField && ((PreField) object).isVariable())
			--this.variablePreFields;
		return result;
	}

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreFieldList))
			return false;

		PreFieldList preFieldList = (PreFieldList) object;

		if (this.size() != preFieldList.size())
			return false;
		
		for (PreField preField : this)
			if (!preFieldList.contains(preField))
				return false;

		return true;
	}

	@Override
	public PreFieldList clone() {
		return new PreFieldList(this.fieldCodeIndex, this.opcode, this);
	}
}
