/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.behaviors;

/**
 * An entity that is a threat to the spaceship.
 * @author Joe Kiniry
 * @version 23 April 2008
 */
public class TowTow {
  //@ initially !towed();

  boolean towing = false;
 
  /**
   * @return Are you currently towing or being towed?
   */
  boolean towed() {
    return towing;
  }

  /**
   * You are now towing or being towed.
   */
  //@ ensures towed();
  void tow() {
    towing = true;
  }
}
