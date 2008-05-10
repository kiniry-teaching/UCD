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
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The door when open. */
  private transient boolean my_openDoor;
  /** The door when closed. */
  private transient boolean my_closedDoor;

  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    return my_closedDoor;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return my_openDoor;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    boolean answer;
    if (closed() || opened()) {
      answer = false;
    } else {
      answer = true;
    }
    return answer;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    if (opened()) {
      my_openDoor = false;
    }
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    if (closed()) {
      my_closedDoor = false;
    }
  }

  public void animate() {
    // TODO Auto-generated method stub

  }

  public Animation animation() {
    animate();
    // TODO Auto-generated method stub
    return null;
  }

  public void animation(final Animation the_animation) {
    // TODO Auto-generated method stub

  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
