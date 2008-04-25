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
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * Is the barrier closed?
   */
  private boolean my_barrier_status = true;
  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    return my_barrier_status;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return !my_barrier_status;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    assert false; //@ assert false;
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    assert false; //@ assert false;
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
