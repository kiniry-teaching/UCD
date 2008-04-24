package thrust.entities;

import thrust.physics.PhysicsClass;

/**
 * Entities whose position or orientation do not change.
 * @author Magdalena Zieniewicz (mazienie@gmail.com)
 * @version 24 April 2008
 */

public class StaticEntityClass extends DynamicEntityClass {
  
    /**
     * @return A new static entity with this position and orientation.
     * @param the_position the immutable position.
     * @param the_orientation the immutable orientation.
     */
  
private PhysicsClass physics;
  
  
  public StaticEntityClass(){
   physics = new PhysicsClass();
  }
  
    //@ ensures position().equals(the_position);
    //@ ensures orientation().equals(the_orientation);
    public static StaticEntity make(double[] the_position,
                                    double the_orientation) {
      assert false; //@ assert false;
      return null;
    }

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#mass()
     */
    //@ ensures \result == 0;
    public double mass(){
      return physics.mass();
    }

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#velocity()
     */
    //@ ensures \result[0] == 0 & \result[1] == 0;
    public double[] velocity(){
      return physics.velocity();
    }
    

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#acceleration()
     */
    //@ ensures \result[0] == 0 & \result[1] == 0;
    public double[] acceleration(){
      return physics.acceleration();
    }

    /* (non-Javadoc)
     * @see thrust.physics.PhysicsInterface#momentum()
     */
    //@ ensures \result == 0;
    public double momentum(){
      return physics.momentum();
    }

    //@ public invariant (* All queries are constant. *);
    //@ public constraint position() == \old(position());
    //@ public constraint orientation() == \old(orientation());

    /*@ public invariant (* Mass, velocity, acceleration, and momentum
      @                     are all zero. *);
      @*/
  }


