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

  /**holds whether barrier is open or not.*/
  private boolean my_opened;
  /** holds whether barrier is closed or not.*/
  private boolean my_closed;
  /**holds the position.*/
  private double[] my_position;
  /**holds the orientation.*/
  private double my_orientation;
  /**holds the acceleration.*/
  private double[] my_acceleration;
  /**holds the mass.*/
  private double my_mass;
  /**holds the velocity.*/
  private double[] my_velocity;
  /**the name of the shape.*/
  private String my_shapename;
  /** the  shape of the barrier.*/
  private Shape my_shape;
  /** the state of the barrier.*/
  private byte my_state;
  /**the color of the barrier.*/
  private Color my_color;
  /**the entity.*/
  private StaticEntity my_entity;
  /**the animation.*/
  private Animation my_animation;

  public Barrier(final double[] the_position,
                 final double the_orientation,
                 final double[] the_acceleration,
                 final double the_mass,
                 final double[] the_velocity,
                 final String the_shapename,
                 final Shape the_shape,
                 final byte the_state) {
    super();
    super.set_Staticstate(the_position, the_orientation,
                            the_acceleration, the_mass,
                            the_velocity, the_shapename,
                            the_shape, the_state);
  }


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

    return my_entity.acceleration();
  }

  public void acceleration(final double[] the_acceleration) {
    my_entity.acceleration(the_acceleration);
  }

  public double mass() {
    return my_mass;

  }

  public void mass(final double the_mass) {
    my_entity.mass(the_mass);
  }

  public double momentum() {
    return my_entity.momentum();
  }

  public double[] velocity() {
    return my_entity.velocity();
  }

  public void velocity(final double[] the_velocity) {
    my_entity.velocity(the_velocity);
  }

  public void render() {
    // TODO Auto-generated method stub

  }



  public Shape shape() {

    return my_shape;
  }

  public void shape(final Shape the_shape) {
    my_shape = the_shape;

  }

  public String shape_name() {
    return my_shapename;
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
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;

  }

  public double gravitational_constant() {
    return my_entity.gravitational_constant();
  }

  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_entity.orientation(the_orientation);
  }

  public double[] position() {
    return my_position;
  }

  public void position(final double[] the_position) {
    my_entity.position(the_position);
  }

  public void simulate(final double a_time_interval) {
    // TODO Auto-generated method stub

  }

  public Color color() {
    return my_color;
  }

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
