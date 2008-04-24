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

import java.awt.Color;
import java.awt.Shape;
import thrust.entities.DynamicEntity;
import thrust.entities.FriendEntity;
import thrust.entities.about.Fuelable;
import thrust.entities.behaviors.Tow;

/**
 * The player's main vehicle.
 * @author jdouglas (jd2088@gmail.com)
 * @version 18 April 2008
 */
public class Spaceship extends DynamicEntity
  implements FriendEntity, Fuelable, Tow {

  /** A spaceship's mass when empty of all fuel is 10000kg. */
  public static final int EMPTY_MASS = 10000;

  /*@ public initially (* The spaceship's initial fuel is 1000 units. *);
    @ public initially fuel() == INITIAL_FUEL;
    @*/
  /** The spaceship's initial fuel is 1000 units. */
  public static final int INITIAL_FUEL = 1000;
  /**
   * The amount of fuel that is contained.
   */
  private int my_fuel;
   /*@ public invariant (* A spaceship's mass when empty of all fuel is
     @                     10000kg. *);
     @ public invariant EMPTY_MASS <= mass();
     @*/
   /**
   * The change in the fuel content by a specific amount of units.
   */
  private int my_fuel_content;
  /**
  * The mass of the fuel.
  */
  private int my_fuel_mass;

  public Spaceship(final double[] the_position,
                   final double the_orientation, final Color the_color,
                   final String the_initial_shape_name,
                   final Shape the_initial_shape,
                   final byte the_initial_state,
                   final double[] the_acceleration,
                   final double[] the_velocity,
                   final double the_mass,
                   final double some_seconds) {

    super();
    super.set_the_state(the_position, the_orientation, the_color,
                   the_initial_shape_name, the_initial_shape,
                   the_initial_state, the_acceleration, the_velocity,
                   the_mass, some_seconds);
  }

  /**
   * returns the maximum amount of fuel that can you contain?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/
  public int maximum_fuel() {
    final int an_max_fuel = 9999;
    return an_max_fuel;
  }
    /**
     * @param the_fuel_change Change your fuel content by this many units.
     */
  public void change_fuel_content(final int the_fuel_change) {
    my_fuel_content = the_fuel_change;
  }

  public int fuel() {
    return my_fuel;
  }
  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
}
  /**
   * @return What is the mass of your fuel?
   */
  //@ ensures \result == fuel() * 1;
  public /*@ pure @*/ int fuel_mass() {
    my_fuel_mass = fuel() * 1;
    return my_fuel_mass;
  }
  /**
   * @return the momentum of an object
   */
  public double momentum()
  {
    final int numberOfElements = 2;
    double[] speed = new double[numberOfElements];
    speed = velocity();
    return mass() * speed[0];
  }
  /**
   * @return the downward acceleration due to gravity.
   */
  public double gravitational_constant()
  {
    final double gravity = -9.81;
    return gravity;
  }
   /**
   * You are now towing or being towed.
   */
  //@ ensures towed();
  public void tow(){
    
  }
  /**
   * @return Are you currently towing or being towed?
   */
  /*@ pure @*/ 
  public boolean towed(){
    return false;
  }
//@ public initially_redundantly mass() == EMPTY_MASS + INITIAL_FUEL;
  /*@ public invariant (* The spaceship is destroyed by the barrier. *);
   * @ public invariant (* The spaceship is destroyed by a bullet. *);
    @ public invariant (* The spaceship is destroyed by the factory. *);
        @ public invariant (* The spaceship is destroyed by the fuel pod. *);
    @ public invariant (* If the spaceship is towing the goal sphere,
        @                     and the spaceship is destroyed, the goal
    @                     sphere is also destroyed. *);
    @ public invariant (* The spaceship is destroyed by the gun turret. *);
    @ public invariant (* The spaceship is not affected by space. *);
    @ public invariant (* The spaceship is not affected by a star. *);
    @ public invariant (* The spaceship is destroyed by the terrain. *);
    @ public invariant (* A spaceship's mass is the sum of its empty mass,
    @                     plus the mass of its fuel, plus the mass of
    @                     the goal sphere, if it is being towed. *);
    @ public invariant mass() == EMPTY_MASS + fuel().mass() +
    @                  (towed() ? GoalSphere.MASS : 0);
    @ public invariant (* The spaceship's shape is always that of a ship. *);
    @ public invariant (* The spaceship's colour is always white. *);
    @ public invariant colour() == thrust.entities.properties.GameColor.WHITE;
    @*/
  }