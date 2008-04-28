/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.animation;

/**
 * An entity that moves or changes independent of the player via an animation.
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 18 April 2008
 */
public class AnimatableClass {
  /**
   * An instance of the Animation class.
   */
  private Animation my_animation = new AnimationClass();
  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation() {
    return this.my_animation;
  }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(final Animation the_animation) {
    this.my_animation = the_animation;
  }

  /**
   * Take a next animation step.
   */
  public void animate() {
    //do something probably with an instance g of Graphics
  }
}
