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

import java.util.Formatter;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {
  /** The Earth's gravity. */
  protected static final double EARTH_GRAVITY = -9.8;

  /** The divisor in our equation for friction. */
  protected static final double FRICTION_FACTOR = 10.0;

  /** The atmospheric frictional constant. */
  private static final double FRICTION_CONSTANT = 0.9;

  /** This entity's acceleration. */
  protected final transient double[] my_acceleration = {0, 0};

  /**
   * This entity's gravitational constant.
   * The default value is Earth gravity.
   */
  protected final transient double my_gravitational_constant = EARTH_GRAVITY;

  /** This entity's mass. */
  protected transient double my_mass;

  /** This entity's orientation. */
  protected transient double my_orientation;

  /** This entity's position.*/
  protected final transient double[] my_position = {0, 0};

  /** This entity's velocity. */
  protected final transient double[] my_velocity = {0, 0};

  /** {@inheritDoc} */
  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1]};
  }

  /** {@inheritDoc} */
  public void acceleration(final double[] the_acceleration) {
    my_acceleration[0] = the_acceleration[0];
    my_acceleration[1] = the_acceleration[1];
  }

  /** {@inheritDoc} */
  public double gravitational_constant() {
    return my_gravitational_constant;
  }

  /** {@inheritDoc} */
  public double mass() {
    return my_mass;
  }

  /** {@inheritDoc} */
  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  /** {@inheritDoc} */
  public double momentum() {
    final double velocity_magnitude =
      Math.abs(my_velocity[0] * my_velocity[0] +
               my_velocity[1] * my_velocity[1]);
    return my_mass * velocity_magnitude;
  }

  /** {@inheritDoc} */
  public double orientation() {
    return my_orientation;
  }

  /** {@inheritDoc} */
  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  /** {@inheritDoc} */
  public double[] position() {
    return new double[] {my_position[0], my_position[1]};
  }

  /** {@inheritDoc} */
  public void position(final double[] the_position) {
    my_position[0] = the_position[0];
    my_position[1] = the_position[1];
  }

  /** {@inheritDoc} */
  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1]};
  }

  /** {@inheritDoc} */
  public void velocity(final double[] the_velocity) {
    my_velocity[0] = the_velocity[0];
    my_velocity[1] = the_velocity[1];
  }

  /**
   * The default simulation of each dynamic entity is to update
   * its position based upon its current velocity, and update its
   * velocity based upon its current accelleration.
   */
  public void simulate(final double some_seconds) {
    // update entity position
    my_position[0] += my_velocity[0] * some_seconds;
    my_position[1] += my_velocity[1] * some_seconds;
    // update entity velocity due to acceleration
    my_velocity[0] += my_acceleration[0] * some_seconds;
    my_velocity[1] += my_acceleration[1] * some_seconds;
  }

  /**
   * Update this entity's velocity due to gravity.
   */
  protected void simulate_gravity(final double some_seconds) {
    my_velocity[1] += my_acceleration[1] * some_seconds +
      my_gravitational_constant * some_seconds;
  }

  /**
   * Update this entity's velocity due to friction.
   */
  protected void simulate_friction(final double some_seconds) {
    my_velocity[0] *= FRICTION_CONSTANT;
  }

  /** {@inheritDoc} */
  public String toString() {
    final Formatter a_formatter = new Formatter(new StringBuilder());
    a_formatter.format("p: (%5.2f,%5.2f) v: (%5.2f,%5.2f) a: <%5.2f,%5.2f>",
                       my_position[0], my_position[1],
                       my_velocity[0], my_velocity[1],
                       my_acceleration[0], my_acceleration[1]);
    return a_formatter.toString();
  }
}
