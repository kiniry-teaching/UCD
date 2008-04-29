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

import java.awt.Color;

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 *  Edited by Ben Fitzgerald 28/04/2008
 */
public class GunTurret extends StaticEntity
  implements EnemyEntity {

  public AI attack() {
    // TODO attack getter method stub
    return null;
  }

  public void attack(final AI the_behavior) {
    // TODO attack getter method stub
  }

  public AI disturb() {
    // TODO disturb getter method stub
    return null;
  }

  public void disturb(final AI the_behavior) {
    // TODO disturb setter method stub
  }

  public void simulate(final double some_seconds) {
    // TODO simulate method stub
  }

  public Color color() {
    // TODO color getter method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO color setter  method stub
  }
  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == java.awt.Color.GREEN;
    @*/
}
