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
 * @author Stephen Murphy (Stephen.Murphy.1@ucdconnect.ie)
 * @version 25 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {

  /** the_position the initial position. */
  private double[] my_position;

  /** the_orientation the initial orientation.*/
  private double my_orientation;

  /** the_acceleration the initial acceleration. */
  private double my_acceleration;

  /** the_grav_constant the initial gravitational constant. */
  private double my_grav_constant;

  /** the_mass the initial mass.*/
  private double my_mass;

  /** the_velocity the initial velocity. */
  private double[] my_velocity;


  /**
   * @return A new dynamic entity with the given physical state.
   * @param the_position the initial position.
   * @param the_orientation the initial orientation.
   * @param the_acceleration the initial acceleration.
   * @param the_grav_constant the initial gravitational constant.
   * @param the_mass the initial mass.
   * @param the_velocity the initial velocity.
   */
  public static DynamicEntity make(final double[] the_position,
                                   final double the_orientation,
                                   final double[] the_acceleration,
                                   final double the_grav_constant,
                                   final double the_mass,
                                   final double[] the_velocity) {
    assert false; //@ assert false;
    return null;
  }
}
