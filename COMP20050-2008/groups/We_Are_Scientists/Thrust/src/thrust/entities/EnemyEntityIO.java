package thrust.entities;

import thrust.entities.behaviors.AI;

/**
 * Enemy Entity input / output.
 *
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 4 May 2008
 */
public class EnemyEntityIO implements EnemyEntity {
  /**
   * The bullet's/turret's disturb behavior.
   */
  private transient AI my_disturb;
  /**
   * The bullet's/turret's attack behavior.
   */
  private transient AI my_attack;

  public boolean an_Attack() {
    return true;

  }

  public AI attack() {
    return my_attack;
  }

  public void attack(final AI the_behavior) {
    my_attack = the_behavior;
  }

  public AI disturb() {
    return my_disturb;
  }

  public void disturb(final AI the_behavior) {
    my_disturb = the_behavior;
  }
}
