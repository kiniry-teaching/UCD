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

import thrust.animation.Animatable;
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

  private boolean my_isopen;
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

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
