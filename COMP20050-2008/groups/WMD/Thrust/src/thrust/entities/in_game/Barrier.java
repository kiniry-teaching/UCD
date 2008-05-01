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
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 29 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {

  /**
   * The color of the barrier.
   */
  private Color my_color;
  /**
   * Is the barrier open.
   */
  private boolean my_open;
  /**
   * Is the barrier closed.
   */
  private boolean my_closed;

  /**
   * Make a barrier.
   * @param a_mass
   */

  public Barrier(final double[] a_position,
                 final double an_orientation,
                 final double[] an_acceleration,
                 final double a_mass,
                 final double[] a_velocity,
                 final String an_initial_shape_name,
                 final Shape an_initial_shape,
                 final byte an_initial_state) {

    super();
    super.set_Staticstate(a_position, an_orientation, an_acceleration,
                          a_mass, a_velocity, an_initial_shape_name,
                          an_initial_shape, an_initial_state);


  }

  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    assert false; //@ assert false;
    if (!moving() && !opened()) {
      my_closed = true;
      my_open = false;
    }
    return my_closed;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    assert false; //@ assert false;
    if (!closed() && !moving()) {
      my_open = true;
      my_closed = false;
    }
    return my_open;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    assert false; //@ assert false;
    if (!opened() && !closed()) {
      return true;
    }
    return false;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    assert false; //@ assert false;
    if (opened()) {
      my_open = false;
      my_closed = true;
      //close
    }
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    assert false; //@ assert false;
    if (closed()) {
      my_open = true;
      my_closed = false;
      //open
    }
  }

  /**
   * Take a next animation step.
   */
  public void animate() {
    // TODO Auto-generated method stub

  }

  /**
   * @return What is your animation?
   */
  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * @param the_animation This is your animation.
   */
  public void animation(final Animation the_animation) {
    // TODO Auto-generated method stub
  }

  /**
   * @return What color are you?
   */
  public Color color() {
    // TODO Auto-generated method stub
    return my_color;
  }

  /**
   * This is your color.
   * @the_color the new color.
   */
  public void color(final Color the_color) {
    my_color = the_color;
  }


  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
