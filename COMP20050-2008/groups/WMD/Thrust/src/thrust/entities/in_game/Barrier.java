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
   * The mass of a barrier.
   */
  private double my_barrier_mass;

  /**
   * Constructor.
   * @param a_mass
   */

  public Barrier(final double a_mass) {

    my_barrier_mass = a_mass;

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

  public double[] acceleration() {
    return null;
  }

  public double mass() {
    return my_barrier_mass;
  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Render yourself.
   */
  public void render() {
    // TODO Auto-generated method stub
  }

  /**
   * @return What shape are you?
   */
  public Shape shape() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    // TODO Auto-generated method stub
  }

  /**
   * @return What shape are you?
   */
  public String shape_name() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  public byte state() {
    // TODO Auto-generated method stub
    return 0;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  public void state(final byte the_state) {
    // TODO Auto-generated method stub

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

  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double orientation() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] position() {
    // TODO Auto-generated method stub
    return null;
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
