package de.agra.sat.koselleck.datatypes;

/** imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * 
 * @author Max Nitze
 */
public class ConstraintParameter {
	/**  */
	public final int parameterIndex;
	
	/**  */
	public final int size;
	/**  */
	public final List<Field> fields;
	/**  */
	public final List<Collection<?>> collections;
	
	/**  */
	private int currentCollectionIndex;
	/**  */
	private final int[] indices;
	/**  */
	private final int[] maxIndices;
	
	/**
	 * 
	 * @param component
	 * @param parameterIndex
	 * @param fields
	 */
	public ConstraintParameter(Object component, int parameterIndex, List<Field> fields) {
		this.parameterIndex = parameterIndex;
		
		this.size = fields.size();
		this.fields = fields;
		
		this.collections = new ArrayList<Collection<?>>();
		this.indices = new int[this.size];
		this.maxIndices = new int[this.size];
		for(int i=0; i<this.fields.size(); i++) {
			Collection<?> parameterCollection;
			try {
				parameterCollection = (Collection<?>)this.fields.get(i).get(component);
			} catch (IllegalArgumentException | IllegalAccessException e) {
				throw new IllegalArgumentException("could not access field \"" + this.fields.get(i) +"\"");
			}
			this.collections.add(i, parameterCollection);
			this.indices[i] = 0;
			this.maxIndices[i] = parameterCollection.size();
		}
		this.currentCollectionIndex = 0;
	}
	
	/**
	 * 
	 * @return
	 */
	public int getCurrentIndex() {
		return this.indices[this.currentCollectionIndex];
	}
	
	/**
	 * 
	 * @return
	 */
	public Collection<?> getCurrentCollection() {
		return this.collections.get(this.currentCollectionIndex);
	}
	
	/**
	 * 
	 * @return
	 */
	public Object getCurrentCollectionObject() {
		return this.collections.get(this.currentCollectionIndex).toArray()[this.indices[this.currentCollectionIndex]];
	}
	
	/**
	 * 
	 * @return
	 */
	public boolean isIncrementable() {
		for(int i=0; i<this.size; i++) {
			if(this.indices[i] < this.maxIndices[i]-1)
				return true;
			else
				this.currentCollectionIndex = i+1;
		}
		
		return false;
	}
	
	/**
	 * 
	 * @return
	 */
	public boolean incrementIndex() {
		if(this.indices[this.currentCollectionIndex] < this.maxIndices[this.currentCollectionIndex]-1) {
			++this.indices[this.currentCollectionIndex];
			return true;
		} else if(this.currentCollectionIndex < this.size-1) {
			++this.currentCollectionIndex;
			return true;
		} else
			return false;
	}
	
	/**
	 * 
	 */
	public void resetIndex() {
		for(int i=0; i<this.size; i++)
			this.indices[i] = 0;
		this.currentCollectionIndex = 0;
	}
}
