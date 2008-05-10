package thrust.entities;
import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class EnemyEntityImp implements EnemyEntity {

  /** The disturb behaviour. */
  private transient AI my_disturb;

  /** The attack behaviour. */
  private transient AI my_attack;

  /**
   * @return What is your attack behavior AI?
   */
  public AI attack() {
    return my_attack;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public AI disturb() {
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
