/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Colin Casey (colin.casey@org.com)
 * @author Ciaran Hale (Ciaran.hale@ucdconnect.ie)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class GunTurret extends StaticEntity
  implements EnemyEntity {

  /**
   * @return The turret's attack AI must shoot a bullet toward the spaceship.
   */
  public AI attack() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @param the_behavior The turret's attack AI must shoot a bullet toward
   * the spaceship.
   */
  public void attack(final AI the_behavior) {
    assert false; //@ assert false;
  }

  /**
   * @return The turret's disturb AI must shoot a bullet in a random direction
   * away from the terrain.
   */
  public AI disturb() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * @param the_behavior The turret's disturb AI must shoot a bullet
   * in a random direction away from the terrain.
   */
  public void disturb(final AI the_behavior) {
    assert false; //@ assert false;
  }
  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == java.awt.Color.GREEN;
    @*/
}
