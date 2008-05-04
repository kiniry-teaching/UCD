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


  /**
   * @return A new dynamic entity with the given physical state.
   * @param the_position
   *          the initial position.
   * @param the_orientation
   *          the initial orientation.
   * @param the_acceleration
   *          the initial acceleration.
   * @param the_grav_constant
   *          the initial gravitational constant.
   * @param the_mass
   *          the initial mass.
   * @param the_velocity
   *          the initial velocity.
   */
  public void the_Dynamic_State(final double[] the_position,
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

  public double[] position() {
    return my_position;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] acceleration() {
    return my_acceleration;
  }

  public double mass() {
    return my_mass;
  }

  public double[] velocity() {
    return my_velocity;
  }

  public Color my_Color() {
    return my_color;
  }

  public void my_Color(final Color the_color) {
    my_color = the_color;
  }

}
