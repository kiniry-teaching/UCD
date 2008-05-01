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
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity implements PhysicsInterface {
  /** Acceleration of the entity. */
  private transient double[] my_acceleration;
  /** Gravitational constant. */
  private transient double my_gravConstant;
  /** The mass of the entity. */
  private transient double my_mass;
  /** The velocity of the entity. */
  private transient double[] my_velocity;
  /** The position of the entity. */
  private transient double[] my_position;
  /** The orientation of the entity in radians. */
  private transient double my_orientation;

  /**
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
                                final double the_grav_constant,
                                final double the_mass,
                                final double[] the_velocity) {
    my_position = new double[]{the_position[0], the_position[1]};
    my_orientation = the_orientation;
    my_acceleration = new double[]{the_acceleration[0], the_acceleration[1]};
    my_gravConstant = the_grav_constant;
    my_mass = the_mass;
    my_velocity = new double[]{the_velocity[0], the_acceleration[1]};
  }

  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1] };
  }

  public double gravitational_constant() {
    return my_gravConstant;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return (my_mass * Math.hypot(my_velocity[0], my_velocity[1]));
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    return new double[] {my_position[0], my_position[1] };
  }

  public void simulate(final double some_seconds) {
    for (int i = 0; i < some_seconds; i++) {
      my_position[0] += my_velocity[0];
      my_position[1] += my_velocity[1];
      my_velocity[0] += my_acceleration[0];
      my_velocity[1] += my_acceleration[1];
      my_acceleration[1] += my_gravConstant;
    }
  }

  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1] };
  }
}
