package de.agra.sat.koselleck.backends.datatypes;

/* imports */
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.agra.sat.koselleck.decompiling.constrainttypes.AbstractConstraint;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class AbstractConstraintSet {
	/** COMMENT */
	private Set<AbstractConstraint> basicConstraints;
	/** COMMENT */
	private Set<AbstractConstraint> connectionConstraints;
	/** COMMENT */
	private Set<AbstractConstraint> rangeConstraints;

	/**
	 * COMMENT
	 */
	public AbstractConstraintSet() {
		this.basicConstraints = new HashSet<AbstractConstraint>();
		this.connectionConstraints = new HashSet<AbstractConstraint>();
		this.rangeConstraints = new HashSet<AbstractConstraint>();
	}

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public List<AbstractConstraint> toConstraintList() {
		List<AbstractConstraint> constraintList = new ArrayList<AbstractConstraint>();
		constraintList.addAll(this.basicConstraints);
		constraintList.addAll(this.connectionConstraints);
		constraintList.addAll(this.rangeConstraints);
		return constraintList;
	}

	/**
	 * COMMENT
	 * 
	 * @param basicConstraint
	 * 
	 * @return
	 */
	public boolean addBasicConstraint(AbstractConstraint basicConstraint) {
		return this.basicConstraints.add(basicConstraint);
	}

	/**
	 * COMMENT
	 * 
	 * @param basicConstraints
	 * 
	 * @return
	 */
	public boolean addAllBasicConstraints(Collection<? extends AbstractConstraint> basicConstraints) {
		return this.basicConstraints.addAll(basicConstraints);
	}

	/**
	 * COMMENT
	 * 
	 * @param connectionConstraint
	 * 
	 * @return
	 */
	public boolean addConnectionConstraint(AbstractConstraint connectionConstraint) {
		return this.connectionConstraints.add(connectionConstraint);
	}

	/**
	 * COMMENT
	 * 
	 * @param connectionConstraints
	 * 
	 * @return
	 */
	public boolean addAllConnectionConstraints(Collection<? extends AbstractConstraint> connectionConstraints) {
		return this.connectionConstraints.addAll(connectionConstraints);
	}

	/**
	 * COMMENT
	 * 
	 * @param rangeConstraint
	 * 
	 * @return
	 */
	public boolean addRangeConstraint(AbstractConstraint rangeConstraint) {
		return this.rangeConstraints.add(rangeConstraint);
	}

	/**
	 * COMMENT
	 * 
	 * @param rangeConstraints
	 * 
	 * @return
	 */
	public boolean addAllRangeConstraints(Collection<? extends AbstractConstraint> rangeConstraints) {
		return this.rangeConstraints.addAll(rangeConstraints);
	}

	/**
	 * COMMENT
	 */
	public void clear() {
		this.basicConstraints.clear();
		this.connectionConstraints.clear();
		this.rangeConstraints.clear();
	}
}
