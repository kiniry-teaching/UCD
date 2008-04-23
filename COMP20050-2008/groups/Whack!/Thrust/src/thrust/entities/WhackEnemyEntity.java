package thrust.entities;

import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 23 April 2008
 */
public class WhackEnemyEntity implements EnemyEntity {
  /**
   * implements disturb.
   */
  private AI my_disturb;
  /**
   * implements attack.
   */
  private AI my_attack;
  /**
   * @return What is your attack behavior AI?
   */
  public/*@ pure @*/ AI attack() {
    return my_attack;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public/*@ pure @*/ AI disturb() {
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
