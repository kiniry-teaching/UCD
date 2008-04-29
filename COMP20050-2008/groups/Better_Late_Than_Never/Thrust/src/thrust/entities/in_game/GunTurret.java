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

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GunTurret extends StaticEntity
  implements EnemyEntity {
  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == thrust.entities.properties.GameColor.GREEN;
    @*/

  /** AI holding Bullet's attack AI. */
  private transient AI my_attack;
  /** AI holding Bullet's disturb AI. */
  private transient AI my_disturb;

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
