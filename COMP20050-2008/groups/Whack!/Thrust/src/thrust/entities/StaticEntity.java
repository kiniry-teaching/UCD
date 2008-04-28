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
 * @author David Maguire (David.Maguire.2@ucdconnect.ie)
 * @version 18 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
  //@ public model boolean initialized;
  //@ public initially initialized == false;
  /**array of doubles representing the position.*/
  double[] my_position;
  /**double representing the orientation.*/
  double my_orientation;

  public StaticEntity() {
    super();
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

  public void set_Staticstate(final double[] the_position,
                        final double the_orientation,
                        final double[] the_acceleration,
                        final double the_mass,
                        final double[] the_velocity,
                        final String the_shapename,
                        final Shape the_shape,
                        final byte the_state) {

    super.set_Dynstate(the_position, the_orientation,
                       the_acceleration, the_mass,
                       the_velocity, the_shapename,
                       the_shape, the_state);
  }
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 0;
  public double mass() {
    final double mass = 0;
    return mass;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#velocity()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] velocity() {
    final double [] velocity = new double[]{0, 0};
    return velocity;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration() {
    final double [] acceleration = new double[]{0, 0};
    return acceleration;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum() {
    final double momentum = 0;
    return momentum;
  }

  //@ public invariant (* All queries are constant. *);
  //@ public constraint initialized ==> (position() == \old(position()));
  //@ public constraint initialized ==> (orientation() == \old(orientation()));

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
