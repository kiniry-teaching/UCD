/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Keith Madden (keith.madden@ucdconnect.ie)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.physics.PhysicsInterface;
import java.awt.Color;
import java.awt.Shape;

/**
 * Entities whose position or orientation change.
 * @author Stephen Walker, Keith Madden
 * (stephen.walker@ucdconnect.ie, keith.madden@ucdconnect.ie)
 * @version 29 April 2008
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

  static thrust.physics.Physic my_physics = new thrust.physics.Physic();

  /**
   * Bullet Object.
   */
  static void my_void;

  /**Color storing the color of the entity.*/
  static Color my_Color;

  public DynamicEntity() {
    super();
  }
  public void set_Dynamic_State (final double[] the_position,
                                 final double the_orientation,
                                 final double[] the_acceleration,
                                 final double the_mass,
                                 final double[] the_velocity,
                                 final String the_initial_shape_name,
                                 final Shape the_initial_shape,
                                 final byte the_initial_state) {
    void my_void = set_Dynamic_State(my_physics.position(), my_physics.orientation(), my_physics.acceleration(), my_physics.mass(), my_physics.velocity(), Entity.shape_name(), Entity.shape(), Entity.state());
//the_position = new double[] {the_position[0], the_position[1] };
// the_orientation = my_physics.orientation();
// the_acceleration = new double[]
//{the_acceleration[my_physics.my_speed],
//the_acceleration[my_physics.direction()]};
// my_physics.mass() = the_mass;
// the_velocity = new double[] {the_velocity[0], the_velocity[1]};

    super.set_State(the_initial_shape_name, the_initial_shape,
                    the_initial_state);

  }
  public double gravitational_constant() {
    return my_physics.gravitational_constant();
  }
  public double[] position() {
    return my_physics.position();
  }
  public double orientation() {
    return my_physics.orientation();
  }
  public double[] acceleration() {
    return my_physics.acceleration();
  }
  public double mass() {
    return my_physics.mass();
  }
  public double[] velocity() {
    return my_physics.velocity();
  }
  public void my_Color(final Color the_color) {
    my_Color = the_color;
  }
  public Color my_Color() {
    return my_Color;
  }

}
