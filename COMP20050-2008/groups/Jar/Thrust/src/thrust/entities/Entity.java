/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.entities.properties.GameColor;

import java.awt.Color;
import java.awt.Shape;
import java.util.logging.Logger;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 18 April 2008
 */
public abstract class Entity implements GameColor {
  /** Logger. */
  private static final Logger LOG = Logger.getLogger("Entity Logger");
  /** The name of the shape. */
  private transient String my_shape_name;
  /** The shape object. */
  private transient Shape my_shape;
  /** The state of the entity. */
  private transient byte my_state;
  /** The color of the entity. */
  private transient Color my_color;

  /**
   * Set the initial shape name, shape, and state of this entity.
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   */
  public void set_state(final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state) {
    my_shape_name = the_initial_shape_name;
    my_shape =  the_initial_shape;
    my_state = the_initial_state;
  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    return my_shape_name;
  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ Shape shape() {
    return my_shape;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    my_shape = the_shape;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ requires 0 <= my_state;
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    //@ assert my_state >= 0;
    return my_state;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(final byte the_state) {
    my_state = the_state;
  }

  /**
   * Render yourself.
   */
  public void render() {
    LOG.info("Render " + this.getClass().getName());
  }

  /* (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color()
   */
  public Color color() {
    return my_color;
  }

  /* (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color(java.awt.Color)
   */
  public void color(final Color the_color) {
    my_color = the_color;
  }
}
