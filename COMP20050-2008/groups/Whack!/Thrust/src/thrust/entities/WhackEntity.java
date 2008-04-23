package thrust.entities;

import java.awt.Color;
import java.awt.Shape;
/**
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)#
 * @version 23 April 2008
 *
 */

public class WhackEntity extends Entity {
/**
 * implementing shape.
 */
  private Shape my_shape;
  /**
   * implementing state.
   */
  private byte my_state;
  /**
   * implemeting color.
   */
  private Color my_color;
  /**
   * @return What shape are you?
   */
  public /*@ pure @*/ String shape_name() {
    return my_shape.toString();
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

  }

  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    // TODO Auto-generated method stub
    my_color = the_color;
  }

}
