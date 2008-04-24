package thrust.animation;

/** Animation class.
 * @author Nick McCarthy (nicholas.mccarthy@gmail.com)
 * @version 24 April 2008
 */
public class AnyAnimation implements Animatable {
/** The animation being used.*/
  static Animation my_animation;

  public void animate() { }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

}
