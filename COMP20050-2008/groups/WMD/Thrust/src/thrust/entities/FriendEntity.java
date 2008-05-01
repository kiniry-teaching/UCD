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

/**
 * An entity that is helpful to the spaceship.
 * @author Keith Madden (keith.madden@ucdconnect.ie)
 * @version 30 April 2008
 */
public class FriendEntity {
  /**GoalSphere. */
  static Entity my_goalSphere;
  /**FuelPod. */
  static Entity my_fuelPod;

  /**GoalSphere Method. */
  static /* pure */ Entity goalSphere() {
    return my_goalSphere;
  }

  /**FuelPod Method. */
  static /* pure */ Entity fuelPod() {
    return my_fuelPod;
  }
}
