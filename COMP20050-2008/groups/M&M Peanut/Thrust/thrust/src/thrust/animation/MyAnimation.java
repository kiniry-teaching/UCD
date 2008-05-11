package thrust.animation;
/**
 * @author Naomi O' Reilly
 * @version 18 April 2008
 */
// don't bother reading this.
public class MyAnimation implements Animatable{
private Animation my_animation;
  public void animate() {
    
    
  }
  /**
   * @return What is your animation?
   */
  public Animation animation() {
    return my_animation;
   }
  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(Animation the_animation) {
    the_animation = animation();
    
  }
  
}
