package de.agra.sat.koselleck.backends.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.agra.sat.koselleck.exceptions.IllegalFieldAccessException;

/**
 * ConstraintParameter describes a parameter of a constraint with a list of all
 *  collections to iterate over and the current indices of that.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
public class ConstraintParameter {
	/** the index of the parameter that is described */
	public final int parameterIndex;

	/** count of the collections to iterate over */
	public final int size;
	/** the collections to iterate over */
	public final List<Collection<?>> collections;

	/** the index of the current collection */
	private int currentCollectionIndex;
	/** the indices in the collections */
	private final int[] indices;
	/** the maximum indices in the collections */
	private final int[] maxIndices;

	/**
	 * Constructor for a new constraint parameter.
	 * 
	 * @param component the component
	 * @param parameterIndex the index of the parameter
	 * @param fields a list of the collection fields
	 */
	public ConstraintParameter(Object component, int parameterIndex, List<Field> fields) {
		this.parameterIndex = parameterIndex;

		this.size = fields.size();

		this.collections = new ArrayList<Collection<?>>();
		this.indices = new int[this.size];
		this.maxIndices = new int[this.size];
		for (int i = 0; i < fields.size(); i++) {
			Collection<?> parameterCollection;
			fields.get(i).setAccessible(true);
			try {
				parameterCollection = (Collection<?>)fields.get(i).get(component);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				Logger.getLogger(ConstraintParameter.class).fatal("could not access field \"" + fields.get(i).getName() +"\"");
				throw new IllegalFieldAccessException(fields.get(i));
			}
			this.collections.add(i, parameterCollection);
			this.indices[i] = 0;
			this.maxIndices[i] = parameterCollection.size();
		}
		this.currentCollectionIndex = 0;
	}

	/**
	 * Getter method for the current index.
	 * 
	 * @return the current index
	 */
	public int getCurrentIndex() {
		return this.indices[this.currentCollectionIndex];
	}

	/**
	 * Getter method for the current collection.
	 * 
	 * @return the current collection
	 */
	public Collection<?> getCurrentCollection() {
		return this.collections.get(this.currentCollectionIndex);
	}

	/**
	 * Getter method for the current object of the current collection.
	 * 
	 * @return the current object of the current collection
	 */
	public Object getCurrentCollectionObject() {
		return this.collections.get(this.currentCollectionIndex).toArray()[this.indices[this.currentCollectionIndex]];
	}

	/**
	 * isIncrementable tests if the parameter object can be incremented.
	 * 
	 * @return {@code true} if there is an index of any of the collections that
	 *  can be incremented, {@code false} otherwise
	 */
	public boolean isIncrementable() {
		for (int i = 0; i < this.size; i++)
			if (this.indices[i] < this.maxIndices[i]-1)
				return true;

		return false;
	}

	/**
	 * incrementIndex increments the index of the parameter object.
	 * 
	 * @return {@code true} if there is an index of any of the collections that
	 *  can be incremented, {@code false} otherwise
	 */
	public boolean incrementIndex() {
		if (this.indices[this.currentCollectionIndex] < this.maxIndices[this.currentCollectionIndex]-1) {
			++this.indices[this.currentCollectionIndex];
			return true;
		} else if (this.currentCollectionIndex < this.size-1) {
			++this.currentCollectionIndex;
			return true;
		} else
			return false;
	}

	/**
	 * resetIndex resets all indices of the parameter object to {@code 0}.
	 */
	public void resetIndex() {
		for (int i = 0; i < this.size; i++)
			this.indices[i] = 0;
		this.currentCollectionIndex = 0;
	}
}
