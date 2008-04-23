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
import thrust.animation.EntityAnimation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity implements NeutralEntity, Animatable {
  public Barrier(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_initial_shape_name,
      final Shape the_initial_shape, final byte the_initial_state) {
    
    super();
    super.set_state(the_position, the_orientation, the_acceleration, the_mass,
                    the_velocity, the_initial_shape_name, the_initial_shape,
                    the_initial_state);

  }

  /**
   * The animation of the barrier.
   */
  private EntityAnimation my_animation;
  /**
   * Indicates whether the barrier is open.
   */
  private boolean my_open;
  /**
   * Indicates whether the barrier is moving.
   */
  private boolean my_moving;

  /**
   * @return Are you closed?
   */
  public/*@ pure @*/boolean closed() {
    return !my_open;
  }

  /**
   * @return Are you open?
   */
  public/*@ pure @*/boolean opened() {
    return my_open;
  }

  /**
   * @return Are you moving?
   */
  public/*@ pure @*/boolean moving() {
    return my_moving;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    my_moving = true;
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    my_moving = true;
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

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
}
