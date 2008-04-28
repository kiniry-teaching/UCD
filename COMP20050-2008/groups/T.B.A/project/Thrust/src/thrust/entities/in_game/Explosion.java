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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 18 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {
/**
 * The color of the explosion.
 */
  private Color my_color = Color.ORANGE;

 /**
  *  The animation steps.
  */
  private final Object[] my_animation_steps =
  {".", "*", "@", "#", "@", "*", "."};

/**
 * Current animation step.
 */
  private int my_step;

/**
 * The animation.
 */
  private Animation my_animation = (Animation) my_animation_steps[my_step];
/**
 * Constructor for creating an explosion.
 * @param the_position
 * @param the_orientation
 * @param the_initial_shape_name
 * @param the_initial_shape
 * @param the_inital_state
 */

  public Explosion(final double[] the_position,
                   final double the_orientation,
                   final String the_initial_shape_name,
                   final Shape the_initial_shape,
                   final byte the_inital_state) {

    super.set_state(the_position, the_orientation,
                    my_color, the_initial_shape_name,
                    the_initial_shape, the_inital_state);
  }

  public void animate() {
    if (my_step == my_animation_steps.length - 1) {
      my_step = 0;
    } else
      my_step++;
    animation((Animation) my_animation_steps[my_step]);

  }
  public Animation animation() {
    return my_animation;
  }
  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

}
