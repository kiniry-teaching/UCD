package thrust.entities;

import java.awt.Color;
import java.awt.Shape;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author Patrick Nevin (Patrick.Nevin@ucdconnect.ie)
 * @version 18 April 2008
 */
public class EntityClass extends Entity {
  /**The initial shape name.*/
  private String my_shapeName;
  /**The initial shape.*/
  private Shape my_shape;
  /**The initial state.*/
  private byte my_state;
  /**The color of the Entity.*/
  private Color my_color;
  /**
   * Set the initial shape name, shape, and state of this entity.
   * @param the_initial_shape_name the initial shape name.
   * @param the_initial_shape the initial shape.
   * @param the_initial_state the initial state.
   */
  public void set_state(final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state) {
    this.my_shapeName = the_initial_shape_name;
    this.my_shape = the_initial_shape;
    this.my_state = the_initial_state;
  }
  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    return this.my_shapeName;
  }
  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ Shape shape() {
    return this.my_shape;
  }
  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    this.my_shape = the_shape;
  }
  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ byte state() {
    return this.my_state;
  }
  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(final byte the_state) {
    this.my_state = the_state;
  }

  public Color color() {
    return this.my_color;
  }

  public void color(final Color the_color) {
    this.my_color = the_color;
  }

}
