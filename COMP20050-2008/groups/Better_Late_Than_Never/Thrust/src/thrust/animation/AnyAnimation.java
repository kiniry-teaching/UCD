package thrust.animation;

/** Animation class.
 * @author Nick McCarthy (nicholas.mccarthy@gmail.com)
 * @version 24 April 2008
 */
public class AnyAnimation implements Animatable {
/** The animation being used.*/
  static AnyAnimation my_animation;

  public void animate() {
    // MUST FINISH THIS METHOD.
  }

  public AnyAnimation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

}
