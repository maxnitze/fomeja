package de.agra.fomeja.annotations;

/** imports */
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Variable is an annotation type to annotate a field, that represents a
 *  variable for the class.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Variable {
	int alter() default 0;
}
