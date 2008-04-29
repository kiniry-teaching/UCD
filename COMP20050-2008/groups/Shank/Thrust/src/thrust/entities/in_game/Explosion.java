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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Kevin Lambe (kevlambe@gmail.com)
 * @version 27 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * The frames in the explosion animation.
   */
  private Animation my_animation;
  /**
   * The color of the explosion.
   */
  private Color my_color;

  public void animation(final Animation the_animation)
  {
    my_animation = the_animation;
  }
  public Animation animation()
  {
    return my_animation;
  }
  public void animate()
  {

  }
  public void color(final Color the_color) {
    my_color = the_color;
  }
  public Color color() {
    return my_color;
  }
  public void simulate(final double the_amount) {
  }
}
