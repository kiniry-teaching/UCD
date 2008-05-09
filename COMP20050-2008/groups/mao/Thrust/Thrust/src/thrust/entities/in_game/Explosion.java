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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.physics.*;

/**
 * An explosion.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  private Animation my_animation;
  private PhysicsInterface my_physics = new PhysicsClass();
  
  /**
   * @return What is your animation?
   */
  public /*@ pure @*/ Animation animation(){
    return my_animation;
  }

  /**
   * @param the_animation This is your animation.
   */
  //@ ensures animation() == the_animation;
  public void animation(Animation the_animation){
    my_animation = the_animation;
  }

  /**
   * Take a next animation step.
   */
  public void animate(){
    //...
  }
  
  public void simulate(double time){
    my_physics.simulate(time);
  }
  /**
   * @return What is your acceleration in meters per second squared?
   */
  //@ ensures \result.length == 2;
  public /*@ pure @*/ double[] acceleration(){
   return my_physics.acceleration();
  }

  /**
   * @return What is the gravitational constant?
   */
  public /*@ pure @*/ double gravitational_constant(){
    return my_physics.gravitational_constant();
  }

  /**
   * @return What is your mass in kilograms?
   */
  //@ ensures 0 <= \result;
 public /*@ pure @*/ double mass(){

    return my_physics.mass();
  }

  /**
   * @return What is your momentum in kilograms*meters per second?
   */
  public /*@ pure @*/ double momentum(){
    return my_physics.momentum();
  }

  /**
   * @return What is your orientation in radians?
   */
  public /*@ pure @*/ double orientation(){
    return my_physics.orientation();
  }

  /**
   * @return What is your position in meters from the origin?
   */
  //@ ensures \result.length == 2;
 public  /*@ pure @*/ double[] position(){
   return my_physics.position();
  }

  /**
   * @return What is your velocity in meters per second?
   */
 public  /*@ pure @*/ double[] velocity(){
   return my_physics.velocity();
  }

}
