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
 * @author simon markey (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Animatable_class {
  
  Animation my_animation;
  /**
   * @return What is your animation?
   */
  /*@ pure @*/ Animation animation()
  {return my_animation;}

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  void animation(Animation the_animation)
  {
    
    if(my_animation.equals(the_animation))
      {animate();}
  }

  /**
   * Take a next animation step.
   */
  void animate()
  {//do stuff
   }
  }
}
