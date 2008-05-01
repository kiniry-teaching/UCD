/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Keith Madden (keith.madden@ucdconnect.ie)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author Keith Madden (keith.madden@ucdconnect.ie)
 * @version 30 April 2008
 */
public class EnemyEntity implements EnemyEntityInterface {
/**
 * ai implementation.
 */
  static AI ai = new AI();

  /**
   * @return What is your attack behaviour AI?
   */
  public /*@ pure @*/ AI attack() {
    ai.act();
    return ai.attack();
  }

  /**
   * @return What is your disturb behaviour AI?
   */
  public /*@ pure @*/ AI disturb() {
    ai.disturb(ai) = 0;
    return ai.disturb();
  }

  /**
   * @param the_behavior This is your attack behaviour.
   */
  //@ ensures attack() == the_behavior;
  public void attack(final AI the_behavior) {
    ai = ai.attack(the_behavior);
  }


  /**
   * @param the_behavior This is your disturb behaviour.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(final AI the_behavior) {
    ai = ai.disturb(the_behavior);
  }
}
