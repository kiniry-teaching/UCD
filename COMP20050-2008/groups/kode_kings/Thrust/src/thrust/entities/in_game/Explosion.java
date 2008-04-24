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
 * @author Colin Casey (colin.casey@org.com)
 * @author Ciaran Hale (Ciaran.hale@ucdconnect.ie)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 23 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The frames in the Explosion animation. */
  private Animation my_animation;

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
    assert false;
  }
}
