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

import java.awt.Shape;

import thrust.entities.DynamicEntity;
import thrust.entities.EnemyAI;
import thrust.entities.EnemyEntity;
import thrust.entities.behaviors.AI;

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity implements EnemyEntity {

  public Bullet(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_initial_shape_name,
      final Shape the_initial_shape, final byte the_initial_state) {
    super();
    super.set_dynamic_state(the_position, the_orientation, the_acceleration,
                            the_mass, the_velocity, the_initial_shape_name,
                            the_initial_shape, the_initial_state);
  }

  private EnemyAI my_ai = new EnemyAI();

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 1;
  public double mass() {
    return 1;
  }

  public AI attack() {
    return my_ai.attack();
  }

  public void attack(final AI the_behavior) {
    my_ai.attack(the_behavior);
  }

  public AI disturb() {
    return my_ai.disturb();
  }

  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behavior);
  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
