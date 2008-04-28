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
  
  /** Animation holding animation steps for Explosion class. */
  private Animation my_animation;

  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation() {
    return my_animation;
  }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

  /**
   * Take a next animation step.
   */
  public void animate() {
    my_animation.animate(); // Animatable.animate() method UNFINISHED
  }


}
