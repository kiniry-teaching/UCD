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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.physics.*;

/**
 * A barrier and trigger to block the spaceship's way.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Barrier extends StaticEntity
  implements NeutralEntity, Animatable {
  
  private Animation my_animation;
  private PhysicsInterface my_physics = new PhysicsClass();
  private int my_step_count;
  
  /**
   * @return Are you closed?
   */
  public /*@ pure @*/ boolean closed() {
    assert false; //@ assert false;
    return false;
  }
  
 // added a constant to track the total number of steps in opening and closing and then each call to animate() increments the current count toward opening or closing by one.


  /**
   * @return Are you open?
   */
  public /*@ pure @*/ boolean opened() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * @return Are you moving?
   */
  public /*@ pure @*/ boolean moving() {
    assert false; //@ assert false;
    return false;
  }

  /**
   * Begin closing.
   */
  //@ requires opened();
  public void close() {
    assert false; //@ assert false;
  }

  /**
   * Begin opening.
   */
  //@ requires closed();
  public void open() {
    assert false; //@ assert false;
  }

  /*@ public invariant (* Barriers are always in one of the three states
    @                     of open, closed, or moving. *);
    @*/
  //@ public invariant closed() ==> !opened() & !moving();
  //@ public invariant opened() ==> !closed() & !moving();
  //@ public invariant moving() ==> !closed() & !opened();
  
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
    my_step_count++;
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

 /**
  * Simulate yourself for this many seconds.
  * @param some_seconds the number of seconds to simulate.
  */
 public void simulate(double some_seconds){
   my_physics.simulate(some_seconds);
}
}