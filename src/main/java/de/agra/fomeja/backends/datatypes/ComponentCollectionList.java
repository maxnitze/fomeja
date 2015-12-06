package de.agra.fomeja.backends.datatypes;

/* imports */
import java.util.Collection;
import java.util.LinkedList;

/**
 * COMMENT
 * 
 * @author Max Nitze
 */
public class ComponentCollectionList extends LinkedList<Collection<?>> {
	/** COMMENT */
	private static final long serialVersionUID = -2376646755552799886L;

	/** COMMENT */
	private int componentsSize;

	/**
	 * COMMENT
	 */
	public ComponentCollectionList() {
		this.componentsSize = 0;
	}

	/**
	 * COMMENT
	 * 
	 * @param collections
	 */
	public ComponentCollectionList(Collection<? extends Collection<?>> collections) {
		super(collections);
		this.componentsSize = 0;
		for (Collection<?> collection : collections)
			this.componentsSize += collection.size();
	}

	/* getter/setter methods
	 * ----- ----- ----- ----- ----- */

	/**
	 * COMMENT
	 * 
	 * @return
	 */
	public int getComponentsSize() {
		return this.componentsSize;
	}

	/* overridden methods
	 * ----- ----- ----- ----- ----- */

	@Override
	public boolean add(Collection<?> collection) {
		this.componentsSize += collection.size();
		return super.add(collection);
	}

	@Override
	public boolean addAll(Collection<? extends Collection<?>> collections) {
		for (Collection<?> collection : collections)
			this.componentsSize += collection.size();
		return super.addAll(collections);
	}
}
