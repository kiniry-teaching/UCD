/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 * Edit Ben Fitzgerald on 24/04/2008
 */

package thrust.entities;
import java.awt.Color;
import java.awt.Shape;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Ben Fitzgerald  (ben.fitz@hotmail.com)
 * @version 24 04 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {
/**The entities x and y position.*/
  private double[] my_position;
/**The entities orientation in radians.*/
  private double my_orientation;
/**The entities colour.*/
  private Color my_colour;
/**The entities shape name.*/
  private String my_initial_shape_name;
/**The entities shape.*/
  private Shape my_initial_shape;
/**The entities initial state.*/
  private byte my_initial_state;
/**The entities acceleration.*/
  private double[] my_acceleration;
/**The entities velocity.*/
  private double[] my_velocity;
/**The entities mass.*/
  private double my_mass;
/**The entities momentum.*/
  private double my_momentum;

/**Set the initial.*/
  public void set_State(final double[] the_position,
                                        final double the_orientation,
                                        final Color the_colour,
                                        final String the_initial_shape_name,
                                        final Shape the_initial_shape,
                                        final byte the_initial_state,
                                        final double[] the_acceleration,
                                        final double[] the_velocity,
                                        final double the_mass,
                                        final double the_momentum
  )
  {
    super.set_state(the_initial_shape_name, the_initial_shape,
                    the_initial_state);
    my_position = the_position;
    my_orientation = the_orientation;
    my_colour = the_colour;
    my_acceleration = the_acceleration;
    my_velocity = the_velocity;
    my_mass = the_mass;
    my_momentum = the_momentum;
  }
  /**
   * @return What position do you have?
   * */
  public double[] position()
  {
    return my_position;
  }
  /**
   * @return What orientation do you have?
   * */
  public double orientation()
  {
    return my_orientation;
  }
  /**
   * @return Set entity colour.
   * */
  public void colour(final Color the_colour )
  {
    my_colour = the_colour;
  }
  /**
   * @return What colour do you have?
   * */
  public Color colour()
  {
    return my_colour;
  }
  /**
   * @return What initial_shape_name do you have?
   * */
  public String initial_shape_name()
  {
    return my_initial_shape_name;
  }
  /**
   * @return What initial_shape do you have?
   * */
  public Shape initial_shape()
  {
    return my_initial_shape;
  }
  /**
   * @return What initial_state do you have?
   * */
  public byte initial_state()
  {
    return my_initial_state;
  }
  /**
   * @return What acceleration do you have?
   * */
  public double[] acceleration()
  {
    return my_acceleration;
  }
  /**
   * @return What velocity do you have?
   * */
  public double[] velocity()
  {
    return my_velocity;
  }
  /**
   * @return What mass do you have?
   * */
  public double mass()
  {
    return my_mass;
  }
  /**
   * @return What momentum do you have?
   * */
  public double momentum()
  {
    return my_momentum;
  }

  /**
   * @return What shape name do you have?
   * */
  public String shape_name() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @return What shape are you?
   */
  public Shape shape() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    assert false; //@ assert false;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public byte state() {
    assert false; //@ assert false;
    return 0;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(final byte the_state) {
    assert false; //@ assert false;
  }

  /**
   * Render yourself.
   */
  public void render() {
    assert false; //@ assert false;
  }
}
