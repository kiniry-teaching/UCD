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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {

  /** Animation holding animation steps for Star class. */
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
  
  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
