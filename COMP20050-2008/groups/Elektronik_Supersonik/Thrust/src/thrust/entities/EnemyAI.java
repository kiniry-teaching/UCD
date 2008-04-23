package thrust.entities;

import thrust.entities.behaviors.AI;

public class EnemyAI implements EnemyEntity{
  /**
   * The bullet's disturb behavior.
   */
  private AI my_disturb;
  /**
   * The bullet's attack behavior.
   */
  private AI my_attack;
  public EnemyAI() {
    
  }

  public AI attack() {
    return my_attack;
  }

  public void attack(AI the_behavior) {
    my_attack = the_behavior;
  }

  public AI disturb() {
    return my_disturb;
  }

  public void disturb(AI the_behavior) {
    my_disturb = the_behavior;
  }
}
