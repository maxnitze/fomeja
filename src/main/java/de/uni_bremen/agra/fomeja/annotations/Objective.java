package de.uni_bremen.agra.fomeja.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Objective is an annotation type to annotate a method, that represents an
 *  objective for the class.
 * 
 * @version 1.0.0
 * @author Max Nitze
 */
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Objective {

}
