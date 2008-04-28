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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
//Implemented by roger fri-Apr 25

public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  /**Put java doc here.*/
  private boolean my_isopen;
  /**Put java doc here.*/
  private boolean my_ismoving;

  /**
   * @return Are you closed?
   */

  public /*@ pure @*/ boolean closed() {
    return !my_isopen;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return my_isopen;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    return my_ismoving;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    my_ismoving = true;
    my_isopen = false;
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    my_ismoving = true;
    my_isopen = true;
  }

  public void animate() {
    // TODO Auto-generated method stub
  }

  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }

  public void animation(final Animation the_animation) {
    // TODO Auto-generated method stub
  }

  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void simulate(final double some_seconds) {
    // TODO Auto-generated method stub
  }

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO Auto-generated method stub
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
