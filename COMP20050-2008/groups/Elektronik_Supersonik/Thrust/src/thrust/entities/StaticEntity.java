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
 * @author Elektronik Supersonik (.@.)
 * @version 18 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
  //@ public model boolean initialised;
  //@ public initially initialised == false;

  /**
   * Set the position and orientation of this entity.  You may only
   * call this method once ever per StaticEntity object.
   * @param the_position the immutable position.
   * @param the_orientation the immutable orientation.
   */
  //@ requires !initialised;
  //@ ensures position()[0] == the_position[0];
  //@ ensures position()[1] == the_position[1];
  //@ ensures orientation() == the_orientation;
  //@ ensures initialised;
  public void set_state(final double[] the_position,
                        final double the_orientation,
                        final double[] the_acceleration,
                        final double the_mass,
                        final double[] the_velocity,
                        final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state) {
    super.set_dynamic_state(the_position, the_orientation, the_acceleration,
                            the_mass, the_velocity, the_initial_shape_name,
                            the_initial_shape, the_initial_state);
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 0;
  public double mass() {
    final double ret = 0.0;
    return ret;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] velocity() {
    return new double[] {0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration() {
    return new double[] {0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum() {
    final double ret = 0.0;
    return ret;
  }

  //@ public invariant (* All queries are constant. *);
  //@ public constraint initialised ==> (position() == \old(position()));
  //@ public constraint initialised ==> (orientation() == \old(orientation()));

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
