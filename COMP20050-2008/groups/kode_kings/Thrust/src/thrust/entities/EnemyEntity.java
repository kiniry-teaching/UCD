
/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.entities.behaviors.AI;

/**
 * An entity that is a threat to the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class EnemyEntity extends AI {/*
	 * A re-implementation of the classic C=64 game 'Thrust'.
	 *
	 * @author "Joe Kiniry (kiniry@acm.org)"
	 * @module "COMP 20050, COMP 30050"
	 * @creation_date "March 2007"
	 * @last_updated_date "April 2008"
	 * @keywords "C=64", "Thrust", "game"
	 */

	package thrust.entities;

	import thrust.entities.behaviors.AI;

	/**
	 * An entity that is a threat to the spaceship.
	 * @author Joe Kiniry (kiniry@acm.org)
	 * @version 18 April 2008
	 */
	public interface EnemyEntity {
	  /**
	   * @return What is your attack behavior AI?
	   */
	  /*@ pure @*/ AI attack();

	  /**
	   * @return What is your disturb behavior AI?
	   */
	  /*@ pure @*/ AI disturb();

	  /**
	   * @param the_behavior This is your attack behavior.
	   */
	  //@ ensures attack() == the_behavior;
	  void attack(AI the_behavior);

	  /**
	   * @param the_behavior This is your disturb behavior.
	   */
	  //@ ensures disturb() == the_behavior;
	  void disturb(AI the_behavior);
	}


    /**
     * implements disturb.
     */

  private AI my_disturb_status();
   /**
    * implements attack.
    */

  private AI my_attack_status();

  /**
   * @return What is your attack behavior AI?
   */
  public/*@ pure @*/ AI attack(); {

    return my_attack_status;
  }
  /**
   * @return What is your disturb behavior AI?
   */
  public/*@ pure @*/ AI disturb(); {

    return my_disturb_status;
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(AI the_behavior); {

   my_attack_status = the_behavior;
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
public  void disturb(AI the_behavior); {

my_disturb_status the_behavior;

  }
}
