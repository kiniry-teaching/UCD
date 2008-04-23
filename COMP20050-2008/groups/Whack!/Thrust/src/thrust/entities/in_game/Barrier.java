/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.in_game;

import java.awt.Color;
import java.awt.Shape;
import java.awt.geom.Rectangle2D;

import thrust.physics.*;
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
  implements NeutralEntity, Animatable, Shape, Physics {

  /**holds whether barrier is open or not.*/
  private boolean my_opened;
  /** holds whether barrier is closed or not.*/
  private boolean my_closed;
  /** the  shape of the barrier.*/
  private Shape my_shape;
  /** the state of the barrier.*/
  private byte my_state;


  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    assert false; //@ assert false;
    if (moving()) {
      my_closed = false;
    } else if (!moving() && !opened()) {
      my_closed = true;
    }

    return my_closed;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    assert false; //@ assert false;
    if (moving()) {
      my_opened = false;
    } else if (!moving() && !closed()) {
      my_opened = true;
    }
    return my_opened;
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
      my_closed = true;
      my_opened = false;

    }

  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    assert false; //@ assert false;

    if (closed()) {
      my_opened = true;
      my_closed = false;
    }
  }

  public double[] acceleration() {

    return acceleration();
  }

  public double barrierMass() {

    final double barrierMass = 70000;
    return barrierMass;
  }

  public double momentum() {
    final double speed = 10;
    return barrierMass() * speed;
  }

  public double[] velocity() {
    final double [] acceleration = acceleration();
    final double speed = acceleration[0];
    final double orientation = acceleration[1];
    final double[] velocity = {speed, orientation};
    return velocity;
  }

  public void render() {
    // TODO Auto-generated method stub

  }



  public Shape shape() {

    return my_shape;
  }

  public void shape(final Shape the_shape) {
    final int my_d = 10;
    final int my_a = 20;
    final int my_t = 10;
    final int my_s = 20;
    my_shape = new Rectangle2D.Float(my_d, my_a, my_t, my_s);

  }

  public String shape_name() {
    final String name = "Rectangle";
    return name;
  }

  public byte state() {

    if (closed()) {
      my_state = -1;
    }
    if (moving()) {
      my_state = 0;
    }
    if (opened()) {
      my_state = 1;
    }
    return my_state;
  }

  public void state(final byte the_state) {
    my_state = the_state;
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

  public double orientation() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] position() {
    // TODO Auto-generated method stub
    return null;
  }

  public void simulate(final double a_time_interval) {
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
