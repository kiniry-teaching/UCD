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

import thrust.physics.Physics;
import java.awt.Color;
import java.awt.Shape;

/**
 * Entities whose position or orientation change.
 * @author Stephen Murphy (Stephen.Murphy.1@ucdconnect.ie)
 * @version 25 April 2008
 */
public class DynamicEntity extends Entity {

  /** Instance of Physics class implementing PhysicsInterface. */
  private static Physics my_physics = new Physics();


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
    my_physics.position(the_position);
    my_physics.orientation(the_orientation);
    my_physics.acceleration(the_acceleration);
    my_physics.gravitational_constant();
    my_physics.mass(the_mass);
    my_physics.velocity(the_velocity);

    return null;
  }

  /** Adds Entity stuff to DynamicEntity.
   * @return DynamicEntity with Entity parameters.
   * @param the_shape_name
   * @param the_shape
   * @param the_state
   */
  public void set_entity_state(final String the_initial_shape_name,
                               final Shape the_initial_shape,
                               final byte the_initial_state) {

    super.set_state(the_initial_shape_name, the_initial_shape,
                    the_initial_state);
  }

  public Color color() {
    return super.color();
  }

  public void color(final Color the_color) {
    super.color(the_color);
  }
}
