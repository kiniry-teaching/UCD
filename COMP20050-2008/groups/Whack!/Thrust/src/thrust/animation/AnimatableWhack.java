package thrust.animation;
/**
 * @author Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 21 April 2008
 */

public class AnimatableWhack implements Animatable {
  /**
   * implementing my_animation.
   */
  Animation my_animation;
  /**
   * @return What is your animation?
   */
  public/*@ pure @*/ Animation animation() {
    return my_animation;
  }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(final Animation  the_animation) {

  }

  /**
   * Take a next animation step.
   */
  public void animate() {

  }

}
