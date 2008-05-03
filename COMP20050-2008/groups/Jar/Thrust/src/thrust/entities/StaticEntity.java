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

import java.awt.Shape;

/**
 * Entities whose position and orientation do not change.
 * @author Keith Byrne, Eoghan O'Donovan, Sean Russell (Jar@timbyr.com).
 * @version 18 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
  //@ public model boolean initialized;
  //@ public initially initialized == false;

  /** No mass variable. */
  private static final int NOMASS = 0;

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
  public void set_static_state(final double[] the_position,
                               final double the_orientation,
                               final String the_shape_name,
                               final Shape the_shape,
                               final byte the_state) {
    super.set_dynamic_state(the_position, the_orientation, new double[]{0, 0},
                            0, 0, new double[]{0, 0});
    super.set_state(the_shape_name, the_shape, the_state);
  //@ initialized = true;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 0;
  public double mass() {
    //@ assert super.mass() == 0;
    return NOMASS;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] velocity() {
    return new double[]{0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration() {
    return new double[]{0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum() {
    return NOMASS;
  }

  //@ public invariant (* All queries are constant. *);
  //@ public constraint initialized ==> (position() == \old(position()));
  //@ public constraint initialized ==> (orientation() == \old(orientation()));

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
