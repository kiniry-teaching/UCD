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

/**
 * Entities whose position and orientation do not change.
 * @author jdouglas (kiniry@acm.org)
 * @version 24 April 2008
 */
public abstract class StaticEntity extends DynamicEntity {
  /**
   * number used to initialise the
   * velocity array and acceleration array.
   */
  final int my_numberTwo = 2;
  /**
   * The Position.
   */
  private static double[] position = {0.0, 0.0};

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
  public static StaticEntity set_state(final double[] the_position,
                        final double the_orientation) {
    position = the_position;
    assert false; //@ assert false;
    return null;
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
    final double[] my_velocity = new double[my_numberTwo];
    my_velocity[0] = 0;
    my_velocity[1] = 0;
    return my_velocity;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#acceleration()
   */
  //@ also ensures \result[0] == 0 & \result[1] == 0;
  public double[] acceleration() {
    final double[] my_acceleration = new double[my_numberTwo];
    my_acceleration[0] = 0;
    my_acceleration[1] = 0;
    return my_acceleration;
  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#momentum()
   */
  //@ also ensures \result == 0;
  public double momentum() {
    final double my_momentum = 0;
    return my_momentum;
  }

  //@ public invariant (* All queries are constant. *);
  //@ public constraint initialized ==> (position() == \old(position()));
  //@ public constraint initialized ==> (orientation() == \old(orientation()));

  /*@ public invariant (* Mass, velocity, acceleration, and momentum
    @                     are all zero. *);
    @*/
}
