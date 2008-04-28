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

/**
 * Entities whose position and orientation do not change.
 * @author Roger Thomas (roger.thomas@ucdconnect.ie)
 * @version 25 April 2008
 * Edited by Ben Fitzgerald 28/04/2008
 */
public abstract class StaticEntity extends DynamicEntity {
  //@ public model boolean initialized;
  //@ public initially initialized == false;

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
  /*
   *                                    final double the_orientation,
                                        final Color the_colour,
                                        final String the_initial_shape_name,
                                        final Shape the_initial_shape,
                                        final byte the_initial_state,
                                        final double[] the_acceleration,
                                        final double[] the_velocity,
                                        final double the_mass,
                                        final double the_momentum
   */
  public void set_state(final double[] the_position,
                        final double the_orientation,
                        final Color the_colour,
                        final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state
  )
  {
    super.set_State(the_position, the_orientation,
                    the_colour, the_initial_shape_name,
                    the_initial_shape, the_initial_state);

  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 0;
  public double mass() {
    return 0.0;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] velocity()
  {
    return new double[] {0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration()
  {
    return new double[] {0, 0};
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum()
  {
    return 0.0;
  }

  //@ public invariant (* All queries are constant. *);
  //@ public constraint initialized ==> (position() == \old(position()));
  //@ public constraint initialized ==> (orientation() == \old(orientation()));

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
