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
 * @author David Murphy(05590701)
 * @version 4 May 2008.
 */
public class DynamicEntity extends Entity
  implements PhysicsInterface {
  /**Size of the arrays which store the dynamic variables. **/
  private static final transient int ARRAY_SIZE = 2;
  /**All dynamic entities must have a maximum velocity.**/
  private static final transient int MAX_VELOCITY = 100;
  /**Orientation of the craft in radians. **/
  private transient double my_orientation;
  /**Array that stores the acceleration variables.**/
  private transient double[] my_acceleration;
  /**Array that stores the entity's x and y variables. **/
  private transient double[] my_position;
  /**Mass of the entity.**/
  private transient double my_mass;
  /**Array that stores velocity data.**/
  private transient double[] my_velocity;
  /**The gravitational constant.**/
  public static final transient int GRAV_CONST = (int) 9.8;
  public void set_state(final double[] position , final double orientation,
                           final double[] acceleration ,
                           final double mass , final double[] velocity ,
                           String shape_name , Shape shape , byte state){
    super.set_state(shape_name, shape, state);
    my_orientation = orientation;
    my_mass = mass;
    my_position = new double[]{position[0] , position[1]};
    my_acceleration = new double[]{position[0] , position[1]};
    my_velocity = new double[]{velocity[0] , velocity[1]};
  }
  public double[] acceleration() {
    return new double[]{my_acceleration[0] , my_acceleration[1]};
  }

  public void acceleration(final double[] the_acceleration) {
    if (the_acceleration.length == ARRAY_SIZE) {
      my_acceleration = new double[]{the_acceleration[0] , the_acceleration[1]};
    }
  }

  public double gravitational_constant() {
    return GRAV_CONST;
  }

  public double mass() {
    return my_mass;
  }

  public void mass(double the_mass) {
    if (0 < the_mass) {
      my_mass = the_mass;
    }
  }

  public double momentum() {
    return (int)mass() * (int)velocity()[0];
  }

  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_orientation = the_orientation;
  }

  public double[] position() {
    return my_position;
  }

  public void position(final double[] the_position) {
    if (the_position.length == ARRAY_SIZE) {
      my_position = new double[]{the_position[0] , the_position[1]};
    }
  }
  public void simulate(final double some_seconds) {
    /** update the position.**/
    my_position[0] = my_velocity[0] * some_seconds;
    my_position[1] = my_velocity[1] * some_seconds;
    /**update the velocity**/
    my_velocity[0] = my_acceleration[0] * some_seconds;
    my_velocity[1] = my_acceleration[1] * some_seconds;
    if (my_velocity[0] > MAX_VELOCITY) {
      my_velocity[0] = MAX_VELOCITY;
    }
    if (my_velocity[1] > MAX_VELOCITY) {
      my_velocity[1] = MAX_VELOCITY;
    }
  }

  public double[] velocity() {
    return my_velocity;
  }
  public void velocity(final double[] the_velocity) {
    if (the_velocity.length == ARRAY_SIZE) {
      my_velocity = new double[]{the_velocity[0] , the_velocity[1]};
    }
  }
  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(Color the_color) {
    // TODO Auto-generated method stub
    
  }
}
