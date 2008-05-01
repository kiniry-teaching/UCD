/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Keith Madden (keith.madden@ucdconnect.ie)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.behaviors;

/**
 * The autonomous behaviours that entities exhibit.
 * @author Keith Madden (keith.madden@ucdconnect.ie)
 * @author Stephen Walker (stephen.walker@ucdconnect.ie)
 * @version 30 April 2008
 */
public class AI {
  /**
   * Entity Object.
   */
  static thrust.entities.Entity my_entity = new thrust.entities.Entity();
  /**
   * Attack Variable.
   */
  AI my_attack;
  /**
   * Disturb Variable.
   */
  AI my_disturb;
  /**
   * Perform your behaviour.
   */
  public void act() {
    final AI act =  my_attack;
  }
  public AI attack(AI the_behaviour) {
    my_attack = the_behaviour;
    return my_attack;
  }
  public AI disturb(AI the_behaviour) {
    my_disturb = the_behaviour;
    return my_disturb;
  }
