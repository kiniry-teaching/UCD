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
import java.awt.Shape;
import java.awt.Color;

/**
 * Entities whose position or orientation change.
 * @author David Haughton (dave.haughton@gmail.com)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements PhysicsInterface {

  /**
   * The angle of an object, in radians.
   */
  double my_angleRadians;

  /**
   * The mass of an object.
   */
  double my_mass;

  /**
   * The position of an object.
   */
  double[] my_xyPosition;

  /**
   * The speed of an object.
   */
  double[] my_velocity;

  /**
   * The acceleration of the entity.
   */
  double[] my_acceleration;

  /**
   * The x and y coordinates of the entity.
   */
  double[] my_position;

  /**
   * Simulate yourself for this many seconds.
   */
  double my_seconds;

  /**
   * the momentum of an entity.
   */
  double my_momentum;

  /**
   * Empty constructor.
   */
  public DynamicEntity() {
  }

  public void set_the_state(
          final double[] the_position,
          final double the_orientation, final Color the_color,
          final String the_initial_shape_name,
          final Shape the_initial_shape,
          final byte the_initial_state,
          final double[] the_acceleration,
          final double[] the_velocity,
          final double the_mass,
          final double some_seconds,
          final double the_momentum
  )
  {
    super.set_state(the_initial_shape_name,
                    the_initial_shape, the_initial_state, the_color);
    this.my_angleRadians = the_orientation;
    this.my_velocity = the_velocity;
    this.my_position =  the_position;
    this.my_acceleration = the_acceleration;
    this.my_mass = the_mass;
    this.my_seconds = some_seconds;
  }

  /**
   * @return the_gravitationalConstant
   * returns the gravitational Constant.
   */
  public double gravitational_constant()
  {
    final double the_gravitationalConstant = 9.81;
    return the_gravitationalConstant;
  }

  /**
   * @return the_acceleration
   * returns the current acceleration
   */
  public double[] acceleration()
  {
    return my_acceleration;
  }

  /**
   * @return my_mass
   * returns the mass of the current entity.
   */
  public double mass()
  {
    return my_mass;
  }

  /**
   * @return my_angleRadians
   * returns the current orientation.
   */
  public double orientation()
  {
    return my_angleRadians;
  }

  /**
   * @return my_momentum
   * returns the current entity's
   * momentum.
   */
  public double momentum()
  {
    return my_momentum;
  }

  /**
   * @return the_position
   * returns the current x and y coordinates.
   */
  public double[] position()
  {
    return my_position;
  }

  /**
   * @return my_velocity
   * returns the current velocity.
   */
  public double[] velocity()
  {
    return my_velocity;
  }

  public double simulate()
  {
    return my_seconds;
  }

  /**
   * @param the_orientation
   * sets the orientation of the entity.
   */
  public void orientation(final double the_orientation)
  {
    this.my_angleRadians = the_orientation;
  }

  /**
   * @param the_accelerationa
   *  sets the acceleration of the entity.
   */
  public void acceleration(final double[] the_accelerationa)
  {
    this.my_acceleration = the_accelerationa;
  }

  /**
   * @param the_velocity
   * sets the velocity of the entity.
   */
  public void velocity(final double[] the_velocity)
  {
    this.my_velocity = the_velocity;
  }

  /**
   * @param the_positions
   * sets the position of an entity.
   */
  public void position(final double[] the_positions)
  {
    this.my_position =  the_positions;
  }

  /**
   * Simulate yourself for this many seconds.
   * @param some_seconds the number of seconds to simulate.
   */
  public void simulate(final double some_seconds)
  {
    this.my_seconds = some_seconds;
  }

  /**
   * @param the_momentum
   * sets the momentum of the current entity.
   */
  public void momentum(final double the_momentum)
  {
    this.my_momentum = the_momentum;
  }

  /**
   * @param the_mass
   * sets the mass of the entity.
   */
  public void mass(final double the_mass)
  {
    this.my_mass = the_mass;
  }

}
