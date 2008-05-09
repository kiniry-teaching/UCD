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
import thrust.entities.about.*;
import thrust.physics.PhysicsClass;
import thrust.physics.PhysicsInterface;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class FuelPod extends StaticEntity
  implements NeutralEntity, Fuelable {
  /*@ public invariant (* A fuel pod is destroyed by a bullet. *);
    @ public invariant (* The fuel pod is not affected by the goal sphere. *);
    @ public invariant (* The fuel pod is not affected by the spaceship. *);
    @ public invariant (* A fuel pod's color is always yellow. *);
    @ public invariant color() == thrust.entities.properties.GameColor.YELLOW;
    @ public invariant (* A fuel pod's 'fuel' lettering color is
    @                     dictated by the amount of fuel it contains. *);
    @*/
  public static final int INITIAL_FUEL = 1000;
  
  private PhysicsInterface my_physics = new PhysicsClass();
  private Fuelable my_fuelable = new FuelableClass(INITIAL_FUEL, INITIAL_FUEL);
  
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
 /**
  * @return Are you currently towing or being towed?
  */
 /*@ pure @*/ boolean towed(){
   //...
   return false;
 }

 /**
  * You are now towing or being towed.
  */
 //@ ensures towed();
 public void tow(){
   
 }
 /**
  * @return How much fuel do you contain?
  */
 public int fuel() {
   return my_fuelable.fuel();
 }

 /**
  * @return What is the mass of your fuel?
  */
 public int fuel_mass() {
   return my_fuelable.fuel_mass();
 }

 /**
  * @return How much fuel can you contain?
  */
 public int maximum_fuel() {
   return my_fuelable.maximum_fuel();
 }
 
 /**
  * @param the_fuel_content This many units is your fuel content.
  */
 //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
 //@ ensures fuel() == the_fuel_content;
 public void set_fuel_content(int the_fuel_content) {
  my_fuelable.set_fuel_content(the_fuel_content);
 }

 public void change_fuel_content(int the_fuel_change) {
   my_fuelable.change_fuel_content(the_fuel_change);
  }
 
  
}
 
