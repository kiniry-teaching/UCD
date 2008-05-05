/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Simon markey,holly baker,ursula redmond ()"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.animation;

/**
 * An entity that moves or changes independent of the player via an animation.
 * @author simon markey (simark@ericom.net)
 * With input from Ursula.
 * @version 18 April 2008
 */
public class Animatable_class {
  /**
   * The animation.
   */
  private transient Animation my_animation;
  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation()
  { return my_animation; }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(final Animation the_animation)
  {
    if (my_animation.equals(the_animation))
    { animate(); }
  }

  /**
   * Take a next animation step.
   */
  public void animate()
  { //do stuff
  }
}
