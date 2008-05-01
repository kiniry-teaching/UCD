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
import java.awt.Shape;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author "Daire O'Doherty (daireod@gmail.com)"
 * @version 30 April 2008
 */
public abstract class Entity implements GameColor {
  /**
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   * @return A new entity with this initial shape name, shape, and state.
   */
  /**the shape.*/
  private transient Shape my_shape;
  /** name of shape.*/
  private transient String my_nameShape;
  /**state of entity.*/
  private byte my_current_state;


  public void set_state(final String the_initial_shape_name,
                            final Shape the_initial_shape,
                            final byte the_initial_state) {
    my_nameShape = the_initial_shape_name;
    my_shape = the_initial_shape;
    my_current_state = the_initial_state;

  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    return my_nameShape;
  }

  /**
   * @return What shape are you?
   */
  public/*@ pure @*/ Shape shape() {
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
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    return my_current_state;

  }
  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(final byte the_state) {
    my_current_state = the_state;
  }

  /**
   * Render yourself.
   */
  public void render() {
    assert false;
  }
}
