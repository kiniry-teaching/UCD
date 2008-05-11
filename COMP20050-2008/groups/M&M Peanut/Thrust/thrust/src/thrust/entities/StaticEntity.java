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

import thrust.physics.Physics

/**
 * Entities whose position and orientation do not change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 * @revised Sean Jago
 * @version 26 April 2008
 */

public class StaticEntity
{
  //@public model boolean initialized;
  //@public initially initialized == false;
   /**
    * check if object is initialized, return true or false.
    */
       private boolean my_initialization;

    /**
     * physics
     */
       private Physics my_physics = new Physics();

    /** 
     *velocity 0
     */
       private double[] my_velocity = {0, 0};

    /** 
     * acceleration 0
     */
       private double[] my acceleration {0, 0};

       public boolean is_initialized()
       {
        return my_initialization;
       }

    /**
    * Set the position and orientation of this entity.  You may only
    * call this method once ever per StaticEntity object.
    * @param the_position the immutable position.
    * @param the_orientation the immutable orientation.
    */
    //@ requires !initialized;
    //@ ensures position()[0] == the_position[0];
    //@ ensures position()[1] == the_position[1];
    //@ ensures orientation() == the_orientation;
    //@ ensures initialized;

    public void set_state(final double[] the_position, final double     the_orientation) 
    {
      my_physics.position(the_position);
      my_physics.orientation(the_orientation);
      my_initialization = true;
    }
   
    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#mass()
     */
    //@ also ensures \result == 0;
    public double mass() 
    {
      return 0;
    }

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#velocity()
     */
    //@ also ensures \result[0] == 0 & \result[1] == 0;
    public double[] velocity() 
    {
      return my_velocity;
    }

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#acceleration()
     */
    //@ also ensures \result[0] == 0 & \result[1] == 0;
    public double[] acceleration() 
    {
      return my_acceleration;
    }
    
    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#momentum()
     */
    //@ also ensures \result == 0;
    public double momentum() 
    {
      return 0;
    }

}