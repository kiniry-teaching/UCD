

package thrust.entities;

import java.awt.Shape;

/**
 * Entities whose position or orientation do not change.
 * @author Stephen Walker (stephen.walker@ucdconnect.ie)
 * @version 29 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
  /**
   * @return A new static entity with this position and orientation.
   * @param the_position the immutable position.
   * @param the_orientation the immutable orientation.
   */
  //@ ensures position().equals(the_position);
  //@ ensures orientation().equals(the_orientation);
  public void set_Staticstate (final double[] the_position,
                              final double the_orientation,
                              final double[] the_acceleration,
                              final double the_mass,
                              final double[] the_velocity,
                              final String the_initial_shape_name,
                              final Shape the_initial_shape,
                              final byte the_initial_state) {

    super.set_State(the_initial_shape_name,
                    the_initial_shape, the_initial_state);

  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 0;
  public abstract double mass();

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ ensures \result[0] == 0 & \result[1] == 0;
  public abstract double[] velocity();

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ ensures \result[0] == 0 & \result[1] == 0;
  public abstract double[] acceleration();

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ ensures \result == 0;
  public abstract double momentum();

  //@ public invariant (* All queries are constant. *);
  //@ public constraint position() == \old(position());
  //@ public constraint orientation() == \old(orientation());

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
