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

import java.util.logging.Logger;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Colin Casey (colin.casey@org.com)
 * @author Ciaran Hale (Ciaran.hale@ucdconnect.ie)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  /** Logger for animation. */
  private static final Logger THE_LOGGER =
    Logger.getLogger(Explosion.class.getName());
  /** The frames in the Explosion animation. */
  private Animation my_animation;
  /** Animation frame counter. */
  private int my_animation_counter;

  /** Explosion Constructor. */
  public Explosion() {

  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

  public void animate() {
    /* When animate is called a frame of animation is played
     * Resets after explosion completes
     */
    my_animation_counter++;
    THE_LOGGER.fine("Explosion animation step " +
                     my_animation_counter + " has been rendered.");
    if (my_animation_counter % 10 == 0) {
      my_animation_counter = 0;
    }
  }
}
