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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The total number of frames in the explosion animation. */
  private static final byte TOTAL_ANIMATION_FRAMES = 10;

  /** The current animation frame that is rendered. */
  private transient byte my_current_frame;

  /** Making something blow up. */
  private transient /*@ non_null @*/ Animation my_animation;

  public void animate() {
    if (my_current_frame < TOTAL_ANIMATION_FRAMES) {
      my_current_frame++;
    }
  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }
}
