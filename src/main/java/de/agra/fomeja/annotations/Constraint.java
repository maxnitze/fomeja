package de.agra.fomeja.annotations;

/** imports */
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Constraint is an annotation type to annotate a method, that represents a
 *  constraint for the class.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Constraint {
	String[] fields() default {};
}
