package thrust.entities;

import java.awt.Color;
import java.awt.Shape;

import thrust.entities.Entity;
import thrust.entities.properties.GameColor;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author David Haughton, jdouglas (kiniry@acm.org)
 * @version 24 April 2008
 */

public class EntityClass extends Entity implements GameColor {

  /**
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   * @return A new entity with this initial shape name, shape, and state.
   */

  /** the_initial_shape_name.
   * is the name of the initial shape
   */
  String my_initial_shape_name;
  /** the_initial_shape.
   * is the shape of the current entity
   */
  Shape my_initial_shape;
/** the_initial_state.
   * is the physical state the current entity
   */
  byte my_initial_state;

  public Entity make(final String the_initial_shape_name,
                            final Shape the_initial_shape,
                            final byte the_initial_state) {


    this.my_initial_shape_name = the_initial_shape_name;
    this.my_initial_shape = the_initial_shape;
    this.my_initial_state = the_initial_state;

    assert false; //@ assert false;
    return null;
  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    return my_initial_shape_name;

  }

  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ Shape shape() {
    return my_initial_shape;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    this.my_initial_shape = the_shape;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    return my_initial_state;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(final byte the_state) {
    this.my_initial_state = the_state;
  }

  /**
   * Render yourself.
   */
  public void render() {

  }

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO Auto-generated method stub

  }
}
