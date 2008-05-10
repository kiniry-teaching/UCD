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

import thrust.animation.Animatable;
import thrust.animation.AnimatableImp;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A blinking star in space.
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {


  /** Star's animation. */
  private transient AnimatableImp my_animation;

  public void animate() {
    my_animation.animate();
  }

  public Animation animation() {
    return my_animation.animation();
  }

  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);
  }

  public Color color() {
    return java.awt.Color.WHITE;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.WHITE) {
      my_Color(java.awt.Color.WHITE);
    }
  }

  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
