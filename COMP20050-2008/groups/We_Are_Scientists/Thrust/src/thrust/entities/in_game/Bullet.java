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

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author simon markey 
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ also ensures \result == 1;
  public double mass() {
    assert false; //@ assert false;
    return 0;
  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
