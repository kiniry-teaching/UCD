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

import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;

/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity, Animatable {

  //@ public invariant (* Terrain and space are disjoint. *);


  /** Animation for Space. */
  private Animation my_animation;
  /** Double holding amount of stars in Space (infinite? :D). */
  private transient double my_stars;

  /** Constructor method. */
  public Space(final double[] the_position,
               final double the_orientation) {

    super();
    super.make(the_position, the_orientation);
  }
  // DON'T KNOW WHAT TO DO WITH THIS METHOD ...
  /**
   * @return What are your stars?"
   */
  public /*@ pure @*/ Collection stars() {

    assert false; //@ assert false;
    return null;
  }
  // CHANGED PARAMETERS FOR METHOD TO ADD STAR, NOW PASSES IN
  // POSITION AND ORIENTATION OF NEW STAR TO CALL.
  /**
   * Add this star to space.
   * @param the_position the position of the star.
   * @param the_orientation the orientation of the star.
   */
  public void add_star(final double[] the_position,
                       final double the_orientation) {

    final Star the_star = new Star(the_position, the_orientation);
    my_stars++;
  }

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
    // my_animation.animate(); // Animatable.animate() method UNFINISHED
  }
}
