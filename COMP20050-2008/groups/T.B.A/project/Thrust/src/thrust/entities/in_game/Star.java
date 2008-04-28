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
 * A blinking star in space.
 * @author jdouglas (jd2088@gmail.com)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {

  /**
   * The animations of the star.
   */
  private final Object[] my_animation_steps = {".", "*"};
  /**
   * The current step.
   */
  private int my_step;
  /**
   * The current animation.
   */
  private Animation my_animation = (Animation) my_animation_steps[my_step];

  public Star(final double[] the_position,
            final double the_orientation, final Color the_color,
            final String the_initial_shape_name,
            final Shape the_initial_shape,
            final byte the_initial_state) {

  super();
    super.set_state(the_position, the_orientation, the_color,
                  the_initial_shape_name,
                  the_initial_shape,
                  the_initial_state);

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


  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
