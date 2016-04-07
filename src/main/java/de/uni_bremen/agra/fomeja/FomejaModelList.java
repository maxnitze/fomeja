package de.uni_bremen.agra.fomeja;

/* imports */
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;

import org.apache.log4j.Logger;

import de.uni_bremen.agra.fomeja.annotations.Variable;
import de.uni_bremen.agra.fomeja.exceptions.FomejaModelCollectionException;

/**
 * COMMENT
 * 
 * @author Max Nitze
 *
 * @param <E> COMMENT
 */
public class FomejaModelList<E> implements List<Object[]> {
	/** COMMENT */
	private FomejaModel<E> modelGenerator;
	/** COMMENT */
	private ModelElement<E> first;
	/** COMMENT */
	private ModelElement<E> last;
	/** COMMENT */
	private int size;
	/** COMMENT */
	private int limit;

	/**
	 * COMMENT
	 * 
	 * @param cls COMMENT
	 */
	public FomejaModelList(Class<E> cls) {
		this(cls, 0);
	}

	/**
	 * COMMENT
	 * 
	 * @param cls COMMENT
	 * @param limit COMMENT
	 */
	public FomejaModelList(Class<E> cls, int limit) {
		this.modelGenerator = new FomejaModel<E>(cls);
		this.first = null;
		this.last = null;
		this.size = 0;
		this.limit = limit;

		this.getNextModelElement();
	}

	/* fomeja methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return COMMENT
	 */
	private void getNextModelElement() {
		if (0 >= this.limit || this.size < this.limit) {
			E element = this.modelGenerator.getNext();
			if (element != null) {
				ModelElement<E> newModelElement = new ModelElement<E>(element, this.last, null);
				if (this.size == 0) {
					this.first = newModelElement;
					this.last = newModelElement;
				} else {
					this.last.setNext(newModelElement);
					this.last = newModelElement;
				}
				++this.size;
			}
		}
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Object[] get(int index) {
		ModelElement<E> curElement = this.first; int i=0;
		while (curElement != null) {
			if (i++ == index)
				return curElement.getOrderedValues();
			else
				curElement = curElement.getNextWithGeneration();
		}

		String message = "index \"" + index + "\" is out of range";
		Logger.getLogger(FomejaModelList.class).error(message);
		throw new IndexOutOfBoundsException(message);
	}

	@Override
	public int indexOf(Object o) {
		ModelElement<E> curElement = this.first; int i=0;
		while (curElement != null) {
			if (curElement.equals(o))
				return i;
			else {
				curElement = curElement.getNext();
				++i;
			}
		}

		return -1;
	}

	@Override
	public int lastIndexOf(Object o) {
		ModelElement<E> curElement = this.last; int i=this.size-1;
		while (curElement != null) {
			if (curElement.equals(o))
				return i;
			else {
				curElement = curElement.getPrev();
				--i;
			}
		}

		return -1;
	}

	@Override
	public boolean contains(Object object) {
		ModelElement<E> e = this.first;
		while (e != null) {
			if (e.equals(object))
				return true;
			else
				e = e.getNext();
		}

		return false;
	}

	@Override
	public boolean containsAll(Collection<?> objects) {
		for (Object object : objects)
			if (!this.contains(object))
				return false;
		return true;
	}

	@Override
	public boolean isEmpty() {
		return this.first == null;
	}

	@Override
	public int size() {
		return this.size;
	}

	@Override
	public Object[] toArray() {
		Object[] array = new Object[this.size];

		ModelElement<E> e = this.first; int i=0;
		while (e != null && i<this.size) {
			array[i] = e.getValue();
			e = e.getNext();
		}

		return array;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T> T[] toArray(T[] array) {
		if (array.length < this.size)
			array = Arrays.copyOf(array, this.size);

		ModelElement<E> e = this.first; int i=0;
		while (e != null && i<this.size) {
			array[i] = (T) e.getValue();
			e = e.getNext();
		}

		return array;
	}

	/* iterator methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public Iterator<Object[]> iterator() {
		return new FomejaListIterator(0);
	}

	@Override
	public ListIterator<Object[]> listIterator() {
		return new FomejaListIterator(0);
	}

	@Override
	public ListIterator<Object[]> listIterator(int index) {
		return new FomejaListIterator(index);
	}

	/* private classes
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 *
	 * @param <T> COMMENT
	 */
	private class ModelElement<T> {
		/** COMMENT */
		private T value;
		/** COMMENT */
		private ModelElement<T> prev;
		/** COMMENT */
		private ModelElement<T> next;

		/** COMMENT */
		private Object[] orderedValues;

		/**
		 * COMMENT
		 * 
		 * @param value COMMENT
		 * @param prev COMMENT
		 * @param next COMMENT
		 */
		private ModelElement(T value, ModelElement<T> prev, ModelElement<T> next) {
			this.setValue(value);
			this.setPrev(prev);
			this.setNext(next);
		}

		/* getter/setter methods
		 * ----- ----- ----- ----- ----- */

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public T getValue() {
			return this.value;
		}

		/**
		 * COMMENT
		 * 
		 * @param value COMMENT
		 */
		public void setValue(T value) {
			this.value = value;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public ModelElement<T> getPrev() {
			return this.prev;
		}

		/**
		 * COMMENT
		 * 
		 * @param next COMMENT
		 */
		public void setPrev(ModelElement<T> prev) {
			this.prev = prev;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public ModelElement<T> getNext() {
			return this.next;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public ModelElement<T> getNextWithGeneration() {
			if (this.next == null)
				getNextModelElement();
			return this.next;
		}

		/**
		 * COMMENT
		 * 
		 * @param next COMMENT
		 */
		public void setNext(ModelElement<T> next) {
			this.next = next;
		}

		/**
		 * COMMENT
		 * 
		 * @return COMMENT
		 */
		public Object[] getOrderedValues() {
			if (this.orderedValues == null)
				this.orderedValues = this.getVarFieldValuesInOrder(this.value);
			return this.orderedValues;
		}

		/**
		 * COMMENT
		 * 
		 * @param element COMMENT
		 * 
		 * @return COMMENT
		 * 
		 * @throws IllegalAccessException 
		 * @throws IllegalArgumentException 
		 */
		private Object[] getVarFieldValuesInOrder(T element) {
			Map<Integer, List<Object>> ordersMap = new HashMap<Integer, List<Object>>();
			int count = 0;
			for (Field field : element.getClass().getDeclaredFields()) {
				Variable fieldVariable = field.getAnnotation(Variable.class);
				if (fieldVariable != null && fieldVariable.order() >= 0) {
					List<Object> orderObjects = ordersMap.get(fieldVariable.order());
					if (orderObjects == null) {
						orderObjects = new ArrayList<Object>();
						ordersMap.put(fieldVariable.order(), orderObjects);
					}

					boolean accessibility = field.isAccessible();
					field.setAccessible(true);
					try {
						orderObjects.add(field.get(element));
					} catch (IllegalArgumentException | IllegalAccessException e) {
						String message = "could not get field \"" + field.getName() + "\" from element \"" + element + "\": " + e.getMessage();
						Logger.getLogger(FomejaModelList.class).error(message);;
						throw new FomejaModelCollectionException(message);
					} finally {
						field.setAccessible(accessibility);
					}

					++count;
				}
			}

			Object[] orderedFieldValues = new Object[count];
			count = 0;
			for (List<Object> objects : ordersMap.values())
				for (Object object : objects)
					orderedFieldValues[count++] = object;

			return orderedFieldValues;
		}
	}

	/**
	 * COMMENT
	 * 
	 * @author Max Nitze
	 */
	private class FomejaListIterator implements ListIterator<Object[]> {
		/** COMMENT */
		private ModelElement<E> current;
		/** COMMENT */
		private ModelElement<E> prev;
		/** COMMENT */
		private int index;

		/**
		 * COMMENT
		 * 
		 * @param startIndex COMMENT
		 */
		public FomejaListIterator(int startIndex) {
			this.current = first;
			this.prev = null;
			for (int i=0; i<startIndex; i++) {
				ModelElement<E> next = this.current.getNextWithGeneration();
				if (next != null) {
					this.prev = this.current;
					this.current = next;
				} else {
					String message = "index \"" + startIndex + "\" is out of range";
					Logger.getLogger(FomejaModelList.class).error(message);
					throw new IndexOutOfBoundsException(message);
				}
			}

			this.index = startIndex;
		}

		@Override
		public boolean hasNext() {
			return this.current != null;
		}

		@Override
		public boolean hasPrevious() {
			return this.prev != null;
		}

		@Override
		public Object[] next() {
			if (this.current != null) {
				ModelElement<E> next = this.current;
				this.prev = this.current;
				this.current = this.current.getNextWithGeneration();
				++this.index;
				return next.getOrderedValues();
			} else {
				String message = "could not get next element at index " + this.index;
				Logger.getLogger(FomejaModelList.class).error(message);;
				throw new NoSuchElementException(message);
			}
		}

		@Override
		public Object[] previous() {
			if (this.prev != null) {
				ModelElement<E> prev = this.prev;
				this.current = this.prev;
				this.prev = this.prev.getPrev();
				--this.index;
				return prev.getOrderedValues();
			} else {
				String message = "could not get previous element at index " + this.index;
				Logger.getLogger(FomejaModelList.class).error(message);;
				throw new NoSuchElementException(message);
			}
		}

		@Override
		public int nextIndex() {
			return this.index;
		}

		@Override
		public int previousIndex() {
			return this.index-1;
		}

		/* unavailable overridden methods
		 * ----- ----- ----- ----- ----- */

		@Override
		public void add(Object[] e) {
			String message = "can not manually manipulate fomeja model list";
			Logger.getLogger(FomejaModelList.class).error(message);
			throw new FomejaModelCollectionException(message);
		}

		@Override
		public void remove() {
			String message = "can not manually manipulate fomeja model list";
			Logger.getLogger(FomejaModelList.class).error(message);
			throw new FomejaModelCollectionException(message);
		}

		@Override
		public void set(Object[] e) {
			String message = "can not manually manipulate fomeja model list";
			Logger.getLogger(FomejaModelList.class).error(message);
			throw new FomejaModelCollectionException(message);
		}
	}

	/* unavailable overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean add(Object[] arg0) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public void add(int index, Object[] element) {
		this.unavailableLogWithException();
	}

	@Override
	public boolean addAll(Collection<? extends Object[]> arg0) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public boolean addAll(int index, Collection<? extends Object[]> c) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public void clear() {
		this.unavailableLogWithException();
	}

	@Override
	public boolean remove(Object arg0) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public Object[] remove(int index) {
		this.unavailableLogWithException();
		return null; // to prevent compiler error
	}

	@Override
	public boolean removeAll(Collection<?> arg0) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public boolean retainAll(Collection<?> arg0) {
		this.unavailableLogWithException();
		return false; // to prevent compiler error
	}

	@Override
	public Object[] set(int index, Object[] element) {
		this.unavailableLogWithException();
		return null; // to prevent compiler error
	}

	@Override
	public List<Object[]> subList(int fromIndex, int toIndex) {
		this.unavailableLogWithException();
		return null; // to prevent compiler error
	}

	/**
	 * COMMENT
	 */
	private void unavailableLogWithException() {
		String message = "can not manually manipulate fomeja model list";
		Logger.getLogger(FomejaModelList.class).error(message);
		throw new FomejaModelCollectionException(message);
	}
}
