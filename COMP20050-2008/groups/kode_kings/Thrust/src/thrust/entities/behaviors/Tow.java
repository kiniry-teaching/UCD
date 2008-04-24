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
 * @author Ciaran Hale (ciaran.hale@ucd.connect.ie)
 * @version 23 April 2008
 */
public interface Tow {
  //@ initially !towed();

  /**
   * @return Are you currently towing or being towed?
   */
  /*@ pure @*/ boolean towed();

  /**
   * You are now towing or being towed.
   */
  //@ ensures towed();
  void tow();
}
