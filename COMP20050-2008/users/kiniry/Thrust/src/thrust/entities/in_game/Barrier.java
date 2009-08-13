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
import java.util.logging.Logger;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  /** The states of a barrier. */
  private static final byte CLOSED = 0, OPENING = 1, CLOSING = 2, OPENED = 3;

  /** The total number of frames in the open/close animation. */
  private static final byte TOTAL_ANIMATION_FRAMES = 10;

  /** The state of this barrier. */
  private transient byte my_state = CLOSED;
  //@ initially my_state == CLOSED;
  /*@ invariant my_state == CLOSED | my_state == CLOSING |
    @           my_state == OPENING | my_state == OPENED;
    @*/

  /** The current animation frame that is rendered. */
  private transient byte my_current_frame;
  //@ invariant (my_current_frame == 0) <==> closed();
  //@ invariant (my_current_frame == TOTAL_ANIMATION_FRAMES) <==> opened();

  /** Moving the barrier open and closed. */
  private transient /*@ non_null @*/ Animation my_animation;

  /** @return Are you closed? */
  public /*@ pure @*/ boolean closed() {
    return my_state == CLOSED;
  }

  /** @return Are you open? */
  public /*@ pure @*/ boolean opened() {
    return my_state == OPENED;
  }

  /** @return Are you moving? */
  public /*@ pure @*/ boolean moving() {
    return (my_state == OPENING | my_state == CLOSING);
  }

  /** Begin closing. */
  //@ requires opened();
  public void close() {
    my_state = CLOSING;
  }

  /** Begin opening. */
  //@ requires closed();
  public void open() {
    my_state = OPENING;
  }

  public void animate() {
    if (my_state == OPENING) {
      my_current_frame++;
    } else if (my_state == CLOSING) {
      my_current_frame--;
    }
    if (my_current_frame == 0) {
      my_state = CLOSED;
    } else if (my_current_frame == TOTAL_ANIMATION_FRAMES) {
      my_state = OPENED;
    }
    Logger.global.info("Animating barrier: frame " +
                       my_current_frame + " rendered.");
  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
