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
 * @author Magdalena Zieniewicz (mazienie@gmail.com)
 * @version 22 April 2008
 */
public class DynamicEntityClass extends DynamicEntity
  implements PhysicsInterface {
  
  
  private PhysicsClass physics;
  
  
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
  
  
   
     public double mass(){
       return physics.mass();
     }

   
     public double[] velocity(){
       return physics.velocity();
     }

 
     public double[] acceleration(){
       return physics.acceleration();
     }

     public double momentum(){
       return physics.momentum();
     }

    public double orientation(){
      return physics.orientation();
    }
    
    public double[] position(){
      return physics.position();
    }
    
    public double gravitational_constant(){
      return physics.gravitational_constant();
    }
    
    public void simulate(double time){
      physics.simulate(time);
    }
}
