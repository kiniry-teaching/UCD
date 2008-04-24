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
  double[] the_acceleration;

  /**
   * The x and y coordinates of the entity.
   */
  double[] the_position;

  public void set_the_state(
          final Shape the_initial_shape,
          final byte the_initial_state,
          final String the_initial_shape_name,
          final double[] the_acceleration,
          final double[] the_position,
          final double[] the_velocity,
          final double the_orientation,
          final double the_mass
  )
  {
    super.set_state(the_initial_shape_name, the_initial_shape,the_initial_state);
    this.my_angleRadians = the_orientation;
    this.my_velocity = the_velocity;
    this.the_position =  the_position;
    this.the_acceleration = the_acceleration;
    this.my_mass = the_mass;
  }



  public double[] acceleration()
  {
    return the_acceleration;
  }

  public double mass()
  {
    return my_mass;
  }

  public double orientation()
  {
    return my_angleRadians;
  }

  public double[] position()
  {
    return the_position;
  }

  public double[] velocity()
  {
    return my_velocity;
  }

  public void orientation(final double the_orientation)
  {
    this.my_angleRadians = the_orientation;
  }

  public void acceleration(final double[] the_accelerationa)
  {
    this.the_acceleration = the_accelerationa;
  }

  public void velocity(final double[] the_velocity)
  {
    this.my_velocity = the_velocity;
  }

  public void position(final double[] the_positions)
  {
    this.the_position =  the_positions;
  }

  public void mass(final double the_mass)
  {
    this.my_mass = the_mass;
  }

}
