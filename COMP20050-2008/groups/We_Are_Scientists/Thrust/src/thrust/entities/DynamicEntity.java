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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public abstract class DynamicEntity extends Entity 
implements PhysicsInterface {
  
      private double[] my_position;
      
      private double my_orientation;
      
      private double[] my_acceleration;
     
      private double my_momentum;
      
      private double my_mass;
      
      private double[] my_velocity;
      
      private Color my_color;
      
      private final double GRAV_CONST = 9.8;
   
  /**
   * @param the_position the initial position.
   * @param the_orientation the initial orientation.
   * @param the_acceleration the initial acceleration.
   * @param the_grav_constant the initial gravitational constant.
   * @param the_mass the initial mass.
   * @param the_velocity the initial velocity.
   */
  public void Dynamic_State(final double[] the_position,final double orientation,final double[] acceleration,final double gravity_constant,final double mass,final double[] velocity, final String shape_name,final Shape shape, final byte state) {
       
  
    super.set_state(shape_name, shape, state);
    my_orientation = orientation;
          my_acceleration[0] = acceleration[0];
          my_acceleration[1] = acceleration[1];
          my_mass = mass;
          my_velocity[0] = velocity[0];
          my_velocity[1] = velocity[1];
  }
    
      public double[] acceleration() {
        return new double[] { my_acceleration[0], my_acceleration[1] };
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
         return new double[] { my_position[0], my_position[1] };
       }
     
       public void simulate(final double some_seconds) {
         assert false;
       }
     
       public double[] velocity() {
         return new double[] { my_velocity[0], my_velocity[1] };
       }
     
       public void velocity(final double[] velocity) {
         my_velocity = new double[] { velocity[0], velocity[1] };
       }
     
       public void orientation(final double orientation) {
         my_orientation = orientation;
       }
     
       public void position(final double[] position) {
         my_position = new double[] { position[0], position[1] };
     }
    
       public void acceleration(final double[] acceleration) {
         my_acceleration = new double[] { acceleration[0], acceleration[1] };
       }
     
       public void mass(final double mass) {
         my_mass = mass;
        
       }
     
       public Color color() {
         return my_color;
       }
     
       public void color(final Color the_color) {
         my_color = the_color;
       }
     }

