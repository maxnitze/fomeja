package de.uni_bremen.agra.fomeja.backends.datatypes;

/* imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ConstraintParameterList {
	/** COMMENT */
	private ConstraintParameter[] params;
	/** COMMENT */
	private int size;

	/**
	 * COMMENT
	 * 
	 * @param size COMMENT
	 */
	public ConstraintParameterList(int size) {
		this.params = new ConstraintParameter[size];
		this.size = size;
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param index COMMENT
	 * 
	 * @return COMMENT
	 */
	public ConstraintParameter get(int index) {
		return this.params[index];
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public int size() {
		return this.size;
	}

	/* increment methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @param index COMMENT
	 * @param component COMMENT
	 * @param fields COMMENT
	 */
	public void add(int index, Object component, List<Field> fields) {
		this.params[index] = new ConstraintParameter(component, fields);
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean isIncrementable() {
		for (int i=this.size-1; i>=0; i--)
			if (this.params[i].isIncrementable())
				return true;
		return false;
	}

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	public boolean increment() {
		for (int i=this.size-1; i>=0; i--) {
			if (this.params[i].increment())
				return true;
			else
				this.params[i].reset();
		}

		return false;
	}

	/**
	 * ConstraintParameter describes a parameter of a constraint with a list of all
	 *  collections to iterate over and the current indices of that.
	 * 
	 * @version 1.0.0
	 * @author Max Nitze
	 */
	public static class ConstraintParameter {
		/** count of the collections to iterate over */
		private int size;
		/** the collections to iterate over */
		private List<Collection<?>> collections;

		/** the index of the current collection */
		private int currentCollectionIndex;
		/** the indices in the collections */
		private int[] indices;
		/** the maximum indices in the collections */
		private int[] maxIndices;

		/**
		 * Constructor for a new constraint parameter.
		 * 
		 * @param component the component
		 * @param parameterIndex the index of the parameter
		 * @param fields a list of the collection fields
		 */
		private ConstraintParameter(Object component, List<Field> fields) {
			this.size = fields.size();

			this.collections = new ArrayList<Collection<?>>();
			this.indices = new int[this.size];
			this.maxIndices = new int[this.size];
			for (int i=0; i<fields.size(); i++) {
				Collection<?> parameterCollection;
				boolean accessibility = fields.get(i).isAccessible();
				fields.get(i).setAccessible(true);
				try {
					parameterCollection = (Collection<?>) fields.get(i).get(component);
				} catch (IllegalArgumentException | IllegalAccessException e) {
					String message = "could not access field \"" + fields.get(i).getName() +"\"";
					Logger.getLogger(ConstraintParameterList.class).fatal(message);
					throw new IllegalArgumentException(message);
				} finally {
					fields.get(i).setAccessible(accessibility);
				}
				this.collections.add(i, parameterCollection);
				this.indices[i] = 0;
				this.maxIndices[i] = parameterCollection.size();
			}
			this.currentCollectionIndex = 0;
		}

		/* getter/setter methods
		 * ----- ----- ----- ----- ----- */

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

		/* increment methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * isIncrementable tests if the parameter object can be incremented.
		 * 
		 * @return {@code true} if there is an index of any of the collections that
		 *  can be incremented, {@code false} otherwise
		 */
		private boolean isIncrementable() {
			for (int i=0; i<this.size; i++)
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
		private boolean increment() {
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
		private void reset() {
			for (int i=0; i<this.size; i++)
				this.indices[i] = 0;
			this.currentCollectionIndex = 0;
		}

		/* misc methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		@Override
		public String toString() {
			return "ConstraintParameter(" + this.size + ", " + this.collections + ")";
		}
	}
}
