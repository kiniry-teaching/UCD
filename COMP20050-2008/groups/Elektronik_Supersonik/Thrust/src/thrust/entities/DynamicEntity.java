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

import java.awt.Color;
import java.awt.Shape;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {
  /**
   * A shape which stores the shape of the entity
   */
  private Shape my_shape;
  /**
   * A string to store the name of the shape.
   */
  private String my_shape_name;
  /** 
   * A byte which stores the state.
   */
  private byte my_state;
  /**
   * An array of doubles to store acceleration.
   */
  private double[] my_acceleration;
  /**
   *  A double to store mass.
   */
  private double my_mass;
  /**
   * A double which stores momentum
   */
  private double my_momentum;
  /**
   * A double which stores the orientation
   */
  private double my_orientation;
  /**
   * An array of doubles storing position
   */
  private double[] my_position;
  /**
   * An array of doubles storing velocity
   */
  private double[] my_velocity;
  /**
   * A color which stores the colour of the entity
   */
  private Color my_color;
  /**
   * A double storing our gravitational constant
   */
  private static final double GRAV_CONST = 0.0000000000667300;
  /**
   * @return A new dynamic entity with the given physical state.
   * @param the_position the initial position.
   * @param the_orientation the initial orientation.
   * @param the_acceleration the initial acceleration.
   * @param the_grav_constant the initial gravitational constant.
   * @param the_mass the initial mass.
   * @param the_velocity the initial velocity.
   */
  public static DynamicEntity make(double[] the_position,
                                   double the_orientation,
                                   double[] the_acceleration,
                                   double the_grav_constant,
                                   double the_mass,
                                   double[] the_velocity) {
    assert false;
    return null;
  }

  public void render() {
    assert false;
  }

  public Shape shape() {
    return my_shape;
  }

  public void shape(Shape the_shape) {
    my_shape = the_shape;
  }

  public String shape_name() {
    return my_shape_name;
  }

  public byte state() {
    return my_state;
  }

  public void state(byte the_state) {
    my_state = the_state;
    
  }

  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1]};
  }

  public double gravitational_constant() {
    return GRAV_CONST;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return my_momentum;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    return new double[] {my_position[0], my_position[1]};
  }

  public void simulate(double some_seconds) {
    assert false;
  }

  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1]};
  }

  public Color color() {
    return my_color;
  }

  public void color(Color the_color) {
    my_color = the_color;
  }
}
