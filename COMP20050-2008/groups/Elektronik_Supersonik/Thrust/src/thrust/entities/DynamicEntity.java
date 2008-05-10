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

import java.awt.Color;
import java.awt.Shape;

import thrust.physics.PhysicsInterface;

/**
 * Entities whose position or orientation change.
 * @author Elektronik Supersonik (.@.)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity implements PhysicsInterface {
  /**
  * A double storing our gravitational constant.
  */
  private static final double GRAV_CONST = 0.0000000000667300;
  /**
   * Velocity cap.
   */
  private static final int MAX_VEL = 30;
  /**
   * Acceleration cap.
   */
  private static final int MAX_ACC = 12;
  /**
   * An Double storing gravity's pull.
   */
  private static final double GRAV_ACCEL = 0.5;
  /**
   * An array of doubles to store acceleration.
   */
  private transient double[] my_acceleration;
  /**
   *  A double to store mass.
   */
  private transient double my_mass;
  /**
   * A double which stores momentum.
   */
  private transient double my_momentum;
  /**
   * A double which stores the orientation.
   */
  private transient double my_orientation;
  /**
   * An array of doubles storing position.
   */
  private transient double[] my_position;
  /**
   * An array of doubles storing velocity.
   */
  private transient double[] my_velocity;
  /**
   * A colour which stores the colour of the entity.
   */
  private transient Color my_color;


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
                                final double the_mass,
                                final double[] the_velocity,
                                final String the_initial_shape_name,
                                final Shape the_initial_shape,
                                final byte the_initial_state) {

    super.set_state(the_initial_shape_name, the_initial_shape,
                    the_initial_state);

    my_orientation = the_orientation;
    my_position = new double[] {the_position[0], the_position[1]};
    my_acceleration = new double[] {the_acceleration[0], the_acceleration[1]};
    my_mass = the_mass;
    my_velocity = new double[] {the_velocity[0], the_velocity[1]};
  }

  public double[] acceleration() {
    return new double[] {my_acceleration[0], my_acceleration[1]};
  }

  public double gravitational_constant() {
    return GRAV_CONST;
  }

  public double mass() {
    return my_mass;
  }

  public double momentum() {
    return my_momentum;
  }

  public double orientation() {
    return my_orientation;
  }

  public double[] position() {
    return new double[] {my_position[0], my_position[1]};
  }

  public void simulate(final double some_seconds) {
    my_position[0] += my_velocity[0] * some_seconds;
    my_position[1] += my_velocity[1] * some_seconds;
    my_velocity[0] += my_acceleration[0] * some_seconds;
    my_velocity[1] += my_acceleration[1] * some_seconds;
    if (my_mass != 0) {
      fixVelocity();
      my_acceleration[1] += some_seconds * GRAV_ACCEL;
      fixAcceleration();
    }
  }

  private void fixVelocity() {
    if (my_velocity[0] > MAX_VEL) {
      my_velocity[0] = MAX_VEL;
    } else {
      if (my_velocity[0] < -MAX_VEL) {
        my_velocity[0] = -MAX_VEL;
      }
    }
    if (my_velocity[1] > MAX_VEL) {
      my_velocity[1] = MAX_VEL;
    } else {
      if (my_velocity[1] < -MAX_VEL) {
        my_velocity[1] = -MAX_VEL;
      }
    }
  }

  private void fixAcceleration() {
    if (my_acceleration[0] > MAX_ACC) {
      my_acceleration[0] = MAX_ACC;
    } else {
      if (my_acceleration[0] < -MAX_ACC) {
        my_acceleration[0] = -MAX_ACC;
      }
    }
    if (my_acceleration[1] > MAX_ACC) {
      my_acceleration[1] = MAX_ACC;
    } else {
      if (my_acceleration[1] < -MAX_ACC) {
        my_acceleration[1] = -MAX_ACC;
      }
    }
  }

  public double[] velocity() {
    return new double[] {my_velocity[0], my_velocity[1]};
  }

  public void velocity(final double[] the_velocity) {
    my_velocity = new double[] {the_velocity[0], the_velocity[1]};
  }

  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  public void position(final double[] the_position) {
    my_position = new double[] {the_position[0], the_position[1]};
  }

  public void acceleration(final double[] the_acceleration) {
    my_acceleration = new double[] {the_acceleration[0], the_acceleration[1]};
  }

  public void mass(final double the_mass) {
    my_mass = the_mass;
  }

  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    my_color = the_color;
  }
}
