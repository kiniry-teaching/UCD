package thrust.entities;

import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class EnemyEntityIO implements EnemyEntity {
  
  private AI my_Disturb;
  
  
  
  private AI my_attack;
      public void EnemyAI() {
       
      }
  /**
   * @return What is your attack behavior AI?
   */
  public/*@ pure @*/ AI attack()
  {return attack;}

  /**
   * @return What is your disturb behavior AI?
   */
  public/*@ pure @*/ AI disturb()
  {return AI;}

  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(AI the_behavior)
  {}

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  void disturb(AI the_behavior);
}
