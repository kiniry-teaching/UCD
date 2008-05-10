package thrust.entities;

import thrust.physics.PhysicsInterface;
import java.awt.Shape;
import java.awt.Color;

/**
 * Entities whose position or orientation change.
 *
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 21 April 2008
 */
public abstract class DynamicEntity extends Entity implements PhysicsInterface {
  /** array of doubles that stores position. */
  private transient double[] my_position;
  /** double containing the entity's orientation. */
  private transient double my_orientation;
  /** array of doubles storing the entity's acceleration. */
  private transient double[] my_acceleration;
  /** double storing the entity's mass. */
  private transient double my_mass;
  /** array of doubles holding the entity's velocity. */
  private transient double[] my_velocity;
  /** Color storing the color of the entity. */
  private transient Color my_color;
  /** double storing the gravitational constant. */
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
  public void set_dynamic_state(final double[] the_position,
                            final double the_orientation,
                            final double[] the_acceleration,
                            final double the_mass, final double[] the_velocity,
                            final String the_shapename, final Shape the_shape,
                            final byte the_state) {
    my_orientation = the_orientation;
    my_acceleration[0] = the_acceleration[0];
    my_acceleration[1] = the_acceleration[1];
    my_mass = the_mass;
    my_velocity[0] = the_velocity[0];
    my_velocity[1] = the_velocity[1];
    super.set_state(the_shapename, the_shape, the_state);

  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
  public double[] position() {
    return new double[] {my_position[0], my_position[1] };
  }

  /**
   * @param the_position This is your position.
   */
  //@ requires the_position.length == 2;
  //@ ensures position()[0] == the_position[0];
  //@ ensures position()[1] == the_position[1];
  public void position(final double[] the_position) {
    my_position = new double[] {the_position[0], the_position[1]};
  }

  /**
   * @return What is your orientation in radians?
   */
  public double orientation() {
    return my_orientation;
  }

  /**
   * @param the_orientation This is your orientation.
   */
  //@ ensures orientation() == the_orientation;
  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1] };
  }

  /**
   * @param the_acceleration This is your acceleration.
   */
  //@ requires the_acceleration.length == 2;
  //@ ensures acceleration()[0] == the_acceleration[0];
  //@ ensures acceleration()[1] == the_acceleration[1];
  public void acceleration(final double[] the_acceleration) {
    my_acceleration = new double[] {the_acceleration[0], the_acceleration[1]};
  }

  /**
   * @return What is the gravitational constant?
   */
  public double gravitational_constant() {
    return GRAV_CONST;
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
  public double mass() {
    return my_mass;
  }

  /**
   * @param the_mass This is your mass.
   */
  //@ requires 0 <= the_mass;
  //@ ensures mass() == the_mass;
  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  /**
   * @return What is your velocity in meters per second?
   */
  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1] };
  }

  /**
   * @param the_velocity This is your velocity.
   */
  //@ requires the_velocity.length == 2;
  //@ ensures velocity()[0] == the_velocity[0];
  //@ ensures velocity()[1] == the_velocity[1];
  public void velocity(final double[] the_velocity) {
    my_velocity = new double[] {the_velocity[0], the_velocity[1]};
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public double momentum() {
    final double m = mass();
    final double[] v = velocity();
    return Math.sqrt((v[0] * m * v[0] * m) + (v[1] * m * v[1] * m));
  }

  /**
   * Simulate yourself for this many seconds.
   * @param some_seconds the number of seconds to simulate.
   */
  public void simulate(final double some_seconds) {
//This will simulate behaviour over some seconds.
  }

  /**
   * Returns the colour.
   * @return the colour
   */
  public Color my_Color() {
    return my_color;
  }

  /**
   * Sets the colour.
   * @param the_color the colour
   */
  public void my_Color(final Color the_color) {
    my_color = the_color;
  }

}
