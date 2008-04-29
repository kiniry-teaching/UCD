

package thrust.entities;

import thrust.entities.properties.GameColor;
import java.awt.Shape;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author Stephen Walker (stephen.walker@ucdconnect.ie)
 * @version 29 April 2008
 */
public abstract class Entity implements GameColor {
  /**
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   * @return A new entity with this initial shape name, shape, and state.
   */
  private String my_shape_name;
  /** Shape to store shape.*/
  private Shape my_shape;
  /** byte to store the state.*/
  private byte my_state;

  public void set_State(final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state) {
    my_shape_name = the_initial_shape_name;
    my_shape = the_initial_shape;
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
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    if (my_state >= 0) {
      return my_state;
    }
    return 0;
  }

  /**
   * This is your physical state.
   * @param my_state the state.
   */
  //@ requires 0 <= my_state;
  //@ ensures state() == the_state;
  public void state(final byte a_state) {
    if (my_state >= 0) {
      my_state = a_state;
    }
  }

  /**
   * Render yourself.
   */
  public void render() {
    assert false;
  }
}
