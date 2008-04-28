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
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * Is the barrier closed? Barrier starts closed.
   */
  private boolean my_barrier_closed_status = true;
  /**
   * Is the barrier open?
   */
  private boolean my_barrier_open_status;
  /**
   * Is the barrier moving?
   */
  private boolean my_barrier_moving_status;
  /**
   * The animations of the barrier.
   */
  private final Object[] my_animation_steps = {"_", "-", ".", "-"};
  /**
   * The current step.
   */
  private int my_step;
  /**
   * The current animation.
   */
  private Animation my_animation = (Animation) my_animation_steps[my_step];
  /**
   * The color.
   */
  private final Color my_color = Color.GRAY;
/**
 * The constructor for a barrier.
 * @param the_position
 * @param the_orientation
 * @param the_initial_shape_name
 * @param the_initial_shape
 * @param the_initial_state
 * @param the_acceleration
 * @param the_velocity
 * @param the_mass
 * @param some_seconds
 * @param the_momentum
 */
  public Barrier(final double[] the_position,
               final double the_orientation,
               final String the_initial_shape_name,
               final Shape the_initial_shape,
               final byte the_initial_state,
               final double[] the_acceleration,
               final double[] the_velocity,
               final double the_mass,
               final double some_seconds,
               final double the_momentum) {
    super.set_the_state(the_position, the_orientation, my_color,
                      the_initial_shape_name, the_initial_shape,
                      the_initial_state, the_acceleration,
                      the_velocity, mass(), some_seconds,
                      the_momentum);

  }
  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    return my_barrier_closed_status;
  }

  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    return my_barrier_open_status;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    return my_barrier_moving_status;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    animate();
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    animate();
  }

  public void animate() {
    if (my_step == my_animation_steps.length - 1) {
      my_step = 0;
      my_barrier_closed_status = true;
      my_barrier_open_status = false;
      my_barrier_moving_status = false;
    } else {
      my_step++;
      my_barrier_moving_status = true;
      my_barrier_closed_status = false;
      my_barrier_open_status = false;
    }
    animation((Animation) my_animation_steps[my_step]);
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
