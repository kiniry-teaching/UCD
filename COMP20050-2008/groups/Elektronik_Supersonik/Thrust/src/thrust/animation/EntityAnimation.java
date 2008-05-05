package thrust.animation;

/**
 *
 * @author Elektronik Supersonik (.@.)
 * @version 05 May 2008
 */
public class EntityAnimation implements Animatable {
  /**
   * The entity's animation.
   */
  private transient Animation my_animation;
  public EntityAnimation() {
  }

  public void animate() {
    // TODO Auto-generated method stub
  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;
  }

}
