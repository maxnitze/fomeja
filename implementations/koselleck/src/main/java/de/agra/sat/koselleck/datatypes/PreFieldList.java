package de.agra.sat.koselleck.datatypes;

/** imports */
import java.util.ArrayList;
import java.util.List;

import de.agra.sat.koselleck.types.Opcode;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class PreFieldList extends ArrayList<PreField> {
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

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean add(PreField preField) {
		if (preField.isVariable())
			++this.variablePreFields;
		return super.add(preField);
	}

	@Override
	public boolean remove(Object o) {
		if (o instanceof PreField && ((PreField) o).isVariable())
			--this.variablePreFields;
		return this.remove(o);
	}

	@Override
	public PreFieldList clone() {
		return new PreFieldList(this.fieldCodeIndex, this.opcode, this);
	}
}
