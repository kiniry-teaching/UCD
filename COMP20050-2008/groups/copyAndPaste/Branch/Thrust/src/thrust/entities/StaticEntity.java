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

import thrust.physics.PhysicsClass;

/**
 * Entities whose position and orientation do not change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 * @revised P Nevin (patrick.nevin@ucdconnect.ie)
 * @version 27 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
//@ public model boolean initialized;
  //@ public initially initialized == false;
  /**
   * flag to indicate if instance of object is initialized.
   */
  private boolean my_initialized; //no need to assign, false by default
  /**
   * create an instance of physics.
   */
  private PhysicsClass my_physics = new PhysicsClass();
  /**
   * static velocity.
   */
  private double[] my_vel = {0, 0};
  /**
   * static acceleration.
   */
  private double[] my_acc = {0, 0};
  /**
   * @return whether instances of this object are initialized
   */
  public boolean is_initialized() {
    return this.my_initialized;
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
  public void set_state(final double[] the_pos, final double the_ori) {
    my_physics.position(the_pos);
    my_physics.orientation(the_ori);
    my_initialized = true;
  }
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 0;
  public double mass() {
    return 0;
  }
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] velocity() {
    return my_vel;
  }
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration() {
    return my_acc;
  }
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum() {
    return 0;
  }

}

