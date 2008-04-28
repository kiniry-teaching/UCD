package thrust.entities;
import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class EnemyEntityImp implements EnemyEntity {
  /**
   * @return What is your attack behavior AI?
   */
  public /*@ pure @*/ AI attack() {
    return null;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public /*@ pure @*/ AI disturb() {
    return null;
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(final AI the_behavior) {

  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(final AI the_behavior) {

  }
}
