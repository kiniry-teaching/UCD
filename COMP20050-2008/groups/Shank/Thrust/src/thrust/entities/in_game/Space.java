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
 * @version 01 May 2008
 * Edited by Roger Thomas 01/05/2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {
  /*
   * @ public invariant (* Space color is always black. *);
   * @ public invariant color() == java.awt.Color.Black;
   */
  /**
   * The frames in the space animation.
   */
  private Animation my_animation;
  /**
   * The color of Space.
   */
  private Color my_color;
  /**
   * Sets the color of Space.
   * @param the_color must be black
   */
  public void color(final Color the_color) {
    my_color = the_color;
  }
  public Color color() {
    return my_color;
  }
  public void animation(final Animation the_animation)
  {
    my_animation = the_animation;
  }
  public Animation animation()
  {
    return my_animation;
  }
  public void animate() {
    my_animation.start();
  }
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
  public void simulate(final double the_amount) {
  }
  public double gravitational_constant() {
    final double d = 9.81;
    return d;
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
