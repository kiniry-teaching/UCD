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

  /** Boolean holding whether Barrier is open. */
  private boolean my_open_state;
  /** Boolean holding whether Barrier is closed. */
  private boolean my_closed_state;
  /** Boolean holding whether Barrier is moving or still. */
  private boolean my_movement;
  /** AnyAnimation holding the animations for Barrier class. */
  private Animation my_animation;

  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    return my_closed_state;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return my_open_state;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    return my_movement;
  }

  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation() {
    return my_animation;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {

    if (opened()) {
      //while (Animation happening)
      my_open_state = false;
      my_closed_state = false;
      my_movement = true;
    } else {
      System.out.print("Barrier must be open to close it.");
    }
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    if (closed()) {
      //while (Animation happening)
      my_open_state = false;
      my_closed_state = false;
      my_movement = true;
    } else {
      System.out.print("Barried must be closed to open it.");
    }
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();


  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

  /**
   * Take a next animation step.
   */
  public void animate() {
    my_animation.animate(); // AnyAnimation.animate() UNFINISHED
  }
}
