/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import thrust.entities.DynamicEntity;
import thrust.entities.EnemyEntity;
import thrust.entities.behaviors.AI;
import java.awt.Shape;

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);

  /** Int holding mass of bullet. */
  private static final int BULLET_MASS = 1;
  /** AI holding Bullet's attack AI. */
  private transient AI my_attack;
  /** AI holding Bullet's disturb AI. */
  private transient AI my_disturb;

  /** Constructor. */

  public Bullet(final double[] the_position, final double the_orientation,
                final double[] the_acceleration,
                final double the_grav_constant, final double the_mass,
                final double[] the_velocity,
                final String the_initial_shape_name,
                final Shape the_initial_shape,
                final byte the_initial_state) {

    super();
    super.make(the_position, the_orientation, the_acceleration,
               the_grav_constant, the_mass, the_velocity);

    super.set_entity_state(the_initial_shape_name, the_initial_shape,
                           the_initial_state);

  }

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;
  public double mass() {
    assert BULLET_MASS == 1 : "Bullet's mass != 1";
    return BULLET_MASS;
  }

  /**
   * @return What is your attack behavior AI?
   */
  public /*@ pure @*/ AI attack() {
    return my_attack;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public /*@ pure @*/ AI disturb() {
    return my_disturb;
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(final AI the_behavior) {
    my_attack = the_behavior;
  }

   /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(final AI the_behavior) {
    my_disturb = the_behavior;
  }

}




