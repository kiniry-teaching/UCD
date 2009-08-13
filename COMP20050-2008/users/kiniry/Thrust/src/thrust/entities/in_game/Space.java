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
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
  /** The stars in space. */
  private final transient /*@ non_null @*/ List my_stars = new ArrayList();

  /** @return What are your stars?" */
  public /*@ pure @*/ Collection stars() {
    return my_stars;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(final Star the_star) {
    my_stars.add(the_star);
  }

  public void animate() {
    final Iterator iterator = my_stars.iterator();
    Animatable animatable;
    while (iterator.hasNext()) {
      animatable = (Animatable)iterator.next();
      animatable.animate();
    }
  }

  public Animation animation() {
    // skip
    return null;
  }

  public void animation(final Animation the_animation) {
    // ignore value of formal parameter and skip
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
