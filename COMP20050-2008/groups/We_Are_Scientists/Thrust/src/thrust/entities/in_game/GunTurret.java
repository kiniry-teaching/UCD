/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import thrust.entities.EnemyEntity;
import thrust.entities.EnemyEntityImp;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

import java.awt.Color;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 *
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class GunTurret extends StaticEntity implements EnemyEntity {

  /** Gun turret's AI. */
  private transient EnemyEntityImp my_ai;

  /**
   * @return The turret's attack AI must shoot a bullet toward the spaceship.
   */
  public AI attack() {
    return my_ai.attack();
  }

  /**
   * @param the_behavior The turret's attack AI must shoot a bullet toward
   * the spaceship.
   */
  public void attack(final AI the_behavior) {
    my_ai.attack(the_behavior);
  }

  /**
   * @return The turret's disturb AI must shoot a bullet in a random direction
   * away from the terrain.
   */
  public AI disturb() {
    return my_ai.disturb();
  }

  /**
   * @param the_behavior The turret's disturb AI must shoot a bullet
   * in a random direction away from the terrain.
   */
  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behavior);
  }

  public Color color() {
    return java.awt.Color.GREEN;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.GREEN) {
      my_Color(java.awt.Color.GREEN);
    }
  }

  /*@ public invariant (* A gun turret always resides on/adjacent to
  @                     the terrain. *);
  @ public invariant (* A gun turret's color is always green. *);
  @ public invariant color() == java.awt.Color.GREEN;
  @*/
}
