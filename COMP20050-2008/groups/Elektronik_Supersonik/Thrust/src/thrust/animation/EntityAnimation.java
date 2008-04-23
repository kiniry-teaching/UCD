package thrust.animation;

public class EntityAnimation implements Animatable{
  /**
   * The entity's animation.
   */
  private Animation my_animation;
  public EntityAnimation() {
    
  }
  
  public void animate() {
    // TODO Auto-generated method stub
    
  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(Animation the_animation) {
    my_animation = the_animation;
  }

}
