package thrust.entities;

import thrust.entities.behaviors.AI;

public class EnemyAI implements EnemyEntity{
  /**
   * The bullet's disturb behavior.
   */
  private transient AI my_disturb;
  /**
   * The bullet's attack behavior.
   */
  private transient AI my_attack;
  public EnemyAI() {
    
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
