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

import java.util.Collection;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author Colin Casey (colin.casey@org.com)
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 24 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The frames in the Space animation. */
  private Animation my_animation;

  /**
   * @return What are your stars?"
   */
  public /*@ pure @*/ Collection stars() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(final Star the_star) {
    assert false; //@ assert false;
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

  //@ public invariant (* Terrain and space are disjoint. *);
}
