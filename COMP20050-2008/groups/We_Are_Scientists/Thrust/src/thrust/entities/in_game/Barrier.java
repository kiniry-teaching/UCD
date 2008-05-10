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
import java.awt.Shape;

import thrust.animation.Animatable;
import thrust.animation.AnimatableImp;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The door when open. */
  private transient boolean my_openDoor;
  /** The door when closed. */
  private transient boolean my_closedDoor;
  /** Barrier's animation. */
  private transient AnimatableImp my_animation;

  public Barrier(final double[] the_position, final double the_orientation,
        final double[] the_acceleration, final double the_mass,
        final double[] the_velocity, final String the_initial_shape_name,
        final Shape the_initial_shape, final byte the_initial_state) {

    super();
    super.set_state(the_initial_shape_name, the_initial_shape,
           the_initial_state);
  }


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
    my_animation.animate();
  }

  public Animation animation() {
    return my_animation.animation();
  }

  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);
  }

  public Color color() {
    return java.awt.Color.YELLOW;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.YELLOW) {
      my_Color(java.awt.Color.YELLOW);
    }
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
