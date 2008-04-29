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
import java.util.Collection;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 * Edited by Ben Fitzgerald 28/04/2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
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

  public void animate() {
    // TODO animate method stub
  }

  public Animation animation() {
    // TODO animation getter method stub
    return null;
  }

  public void animation(final Animation the_animation) {
    // TODO animation setter method stub
  }

  public void simulate(final double some_seconds) {
    // TODO simulate method stub
  }

  public Color color() {
    // TODO color getter method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO color setter  method stub
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
