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
import java.awt.Color;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {
  /**
   * @return A new dynamic entity with the given physical state.
   * @param the_position the initial position.
   * @param the_orientation the initial orientation.
   * @param the_acceleration the initial acceleration.
   * @param the_grav_constant the initial gravitational constant.
   * @param the_mass the initial mass.
   * @param the_velocity the initial velocity.
   */

  static double[] my_position;
  /**double containing the entity's orientation.*/
  static double my_orientation;
  /**array of doubles storing the entity's acceleration.*/
  static double[] my_acceleration;
  /**double storing the entity's mass.*/
  static double my_mass;
  /**array of doubles holding the entity's velocity.*/
  static double[] my_velocity;
  /**Color storing the color of the entity.*/
  Color my_color;

  public DynamicEntity() {
    super();
  }
  public static DynamicEntity make(final double[] the_position,
                                   final double the_orientation,
                                   final double[] the_acceleration,
                                   final double the_mass,
                                   final double[] the_velocity,
                                   final String the_shape_name) {

    my_position = the_position;
    my_orientation = the_orientation;
    my_acceleration = the_acceleration;
    my_mass = the_mass;
    my_velocity = the_velocity;

    return null;
  }
}
