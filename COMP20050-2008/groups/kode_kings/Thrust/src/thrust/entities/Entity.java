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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class Entity implements GameColor {
  /**
   * Set the initial shape name, shape, and state of this entity.
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   */
  public static Entity make(final String the_initial_shape_name,
                            final Shape the_initial_shape,
                            final byte the_initial_state) {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ Shape shape() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(Shape the_shape) {
    assert false; //@ assert false;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    assert false; //@ assert false;
    return 0;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(byte the_state) {
    assert false; //@ assert false;
  }

  /**
   * Render yourself.
   */
  public void render() {
    assert false; //@ assert false;
  }
}
