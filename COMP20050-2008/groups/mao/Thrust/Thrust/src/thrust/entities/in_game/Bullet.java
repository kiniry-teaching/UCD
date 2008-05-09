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

import thrust.entities.DynamicEntity;
import thrust.entities.EnemyEntity;
import thrust.entities.behaviors.AI;
import thrust.physics.PhysicsClass;
import thrust.physics.PhysicsInterface;

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {
  
  private PhysicsInterface my_physics = new PhysicsClass();
  private AI my_attack;
  private AI my_disturb;
  
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;
  public double mass() {
    assert false; //@ assert false;
    return 1;
  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
  
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
  /**
   * @return What is your attack behavior AI?
   */
  public /*@ pure @*/ AI attack(){
    return my_attack;
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public /*@ pure @*/ AI disturb(){
    return my_disturb;
  }
  /**
   * @param the_behavior This is your attack behavior.
   */
  //@ ensures attack() == the_behavior;
  public void attack(AI the_behavior){
    
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  //@ ensures disturb() == the_behavior;
  public void disturb(AI the_behavior){
    
  }
  
}
