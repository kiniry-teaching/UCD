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
import java.util.LinkedList;

import thrust.animation.Animatable;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
  /** Collection of stars objects. */
  private static final LinkedList STARS = new LinkedList();
  /**
   * @return What are your stars?"
   */
  public /*@ pure @*/ Collection stars() {
    //@ assert true;
    return STARS;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(final Star the_star) {
    //@ assert false;
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
