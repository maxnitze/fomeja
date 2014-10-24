package de.agra.sat.koselleck.datatypes;

/** imports */
import java.util.List;

import de.agra.sat.koselleck.types.Opcode;

/**
 * 
 * @author Max Nitze
 */
public class PreClass {
	/**  */
	private final Class<?> clazz;

	/** the opcode of the field */
	private final Opcode fieldCode;
	/**  */
	private final int fieldCodeIndex;

	/**
	 * 
	 * @param clazz
	 * @param fieldCode
	 * @param fieldCodeIndex
	 */
	public PreClass(Class<?> clazz, Opcode fieldCode, int fieldCodeIndex, List<PreClass> preFields) {
		this.clazz = clazz;

		this.fieldCode = fieldCode;
		this.fieldCodeIndex = fieldCodeIndex;
	}

	/** getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * 
	 * @return
	 */
	public Class<?> getClazz() {
		return this.clazz;
	}

	/**
	 * 
	 * @return
	 */
	public Opcode getFieldCode() {
		return this.fieldCode;
	}

	/**
	 * 
	 * @return
	 */
	public int getFieldCodeIndex() {
		return this.fieldCodeIndex;
	}

	/** class methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean equals(Object object) {
		if (!(object instanceof PreClass))
			return false;

		PreClass preClass = (PreClass) object;

		return this.clazz.equals(preClass.clazz);
	}
}
