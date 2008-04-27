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
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  /** The open state of the door. */
  private boolean my_openState;
  /** The closed state of the door. */
  private boolean my_closeState;

  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    return my_closeState;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return my_openState;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    return (!opened() && !closed());
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    if (opened()) {
      my_openState = false;
    }
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    if (closed()) {
      my_closeState = false;
    }
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
