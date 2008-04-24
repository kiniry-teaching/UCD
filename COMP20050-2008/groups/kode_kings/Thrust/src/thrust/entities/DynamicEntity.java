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

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Colin Casey (colin.casey@org.com)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class DynamicEntity extends Entity
  implements PhysicsInterface {

  /**
   * Implementation of Physics methods.
   * @author Colin Casey (colin.casey@org.com)
   * @version 23 April 2008
   */

  /** The force that attracts the spaceship and
   * goal sphere toward the terrain. */
  private static final double GRAVITY_CONSTANT = -9.8;
  /** Increase in the rate of speed of something. */
  protected double[] my_acceleration;
  /** The quantity of matter that an entity contains. */
  protected double my_mass;
  /** The speed of an entity in a given direction. */
  protected double[] my_velocity;
  /** The relative physical direction of entities. */
  protected double my_orientation;
  /** The co-ordinates where an entity is located. */
  protected double[] my_position;;

  public double[] acceleration() {
    final double[] temp = new double[my_acceleration.length];
    System.arraycopy(my_acceleration, 0, temp, 0, my_acceleration.length);
    return temp;
  }

  public double gravitational_constant() {
    return GRAVITY_CONSTANT;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    /* Calculate momentum */
    return ((Math.sqrt((my_velocity[0] * my_velocity[0]) +
                       (my_velocity[1] * my_velocity[1]))) * my_mass);
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    final double[] temp = new double[my_position.length];
    System.arraycopy(my_position, 0, temp, 0, my_position.length);
    return temp;
  }

  public double[] velocity() {
    final double[] temp = new double[my_velocity.length];
    System.arraycopy(my_velocity, 0, temp, 0, my_velocity.length);
    return temp;
  }

  public void position(final double[] the_position) {
    my_position = the_position;
  }

  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  public void velocity(final double[] the_velocity) {
    my_velocity = the_velocity;
  }

  public void acceleration(final double[] the_acceleration) {
    my_acceleration[0] = the_acceleration[0];
    my_acceleration[0] = the_acceleration[0] + GRAVITY_CONSTANT;
  }

  public void simulate(final double some_seconds) {
    /* Calculate new position after time has elapsed */
    my_position[0] = my_position[0] + (my_velocity[0] * some_seconds) +
      ((my_acceleration[0] * some_seconds * some_seconds) / 2);
    my_position[1] = my_position[1] + (my_velocity[1] * some_seconds) +
      ((my_acceleration[1] * some_seconds * some_seconds) / 2);

    /* Calculate new velocity after time has elapsed */
    my_velocity[0] = my_velocity[0] + my_acceleration[0] * some_seconds;
    my_velocity[1] = my_velocity[1] + my_acceleration[1] * some_seconds;
  }
}
