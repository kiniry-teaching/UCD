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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity implements PhysicsInterface {
  /** Acceleration of the entity. */
  private static double[] my_acceleration;
  /** Gravitational constant. */
  private static double my_gravConstant;
  /** The mass of the entity. */
  private static double my_mass;
  /** The velocity of the entity. */
  private static double[] my_velocity;
  /** The position of the entity. */
  private static double[] my_position;
  /** The orientation of the entity in radians. */
  private static double my_orientation;

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
                                   double the_grav_constant, double the_mass,
                                   double[] the_velocity) {
    my_position = the_position;
    my_orientation = the_orientation;
    my_acceleration = the_acceleration;
    my_gravConstant = the_grav_constant;
    my_mass = the_mass;
    my_velocity = the_velocity;
    return null;
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
      System.out.println("Keith whores for food");
    }
  }

  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1] };
  }
}
