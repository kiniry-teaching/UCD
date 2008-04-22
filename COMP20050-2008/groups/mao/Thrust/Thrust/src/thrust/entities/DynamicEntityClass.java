/**
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */


package thrust.entities;

import java.awt.Shape;

import thrust.physics.PhysicsInterface;
import thrust.physics.PhysicsClass;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class DynamicEntityClass extends DynamicEntity
  implements PhysicsInterface {
  
  
  private PhysicsClass physics;
  private Shape shape;
  private byte state;
  
  public DynamicEntityClass(){
   physics = new PhysicsClass();
  }
  
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
                                   double the_grav_constant,
                                   double the_mass,
                                   double[] the_velocity) {
    
 
    assert false; //@ assert false;
    return null;
  }
  
  public  String shape_name(){
    return shape.toString();
  }

  /**
   * @return What shape are you?
   */
  public  Shape shape(){
    return shape;
  }
    
  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(Shape the_shape){
    shape = the_shape;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  //@ ensures 0 <= \result;
  public byte state(){
    return state;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  //@ requires 0 <= the_state;
  //@ ensures state() == the_state;
  public void state(byte the_state){
    state = the_state;
  }

  /**
   * Render yourself.
   */
  public void render(){
    
}
  
}
