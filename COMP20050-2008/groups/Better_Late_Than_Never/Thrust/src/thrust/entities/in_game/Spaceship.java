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
import thrust.entities.FriendEntity;
import thrust.entities.about.Fuelable;
import thrust.entities.behaviors.Tow;

/**
 * The player's main vehicle.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Spaceship extends DynamicEntity
  implements FriendEntity, Fuelable, Tow {
  /*@ public invariant (* A spaceship's mass when empty of all fuel is
    @                     10000kg. *);
    @ public invariant EMPTY_MASS <= mass();
    @*/
  /** A spaceship's mass when empty of all fuel is 10000kg. */
  public static final int EMPTY_MASS = 10000;

  /*@ public initially (* The spaceship's initial fuel is 1000 units. *);
    @ public initially fuel() == INITIAL_FUEL;
    @*/
  /** The spaceship's initial fuel is 1000 units. */
  private static final int INITIAL_FUEL = 1000;
  /** The spaceship's maximum fuel capacity. */
  private static final int MAX_FUEL = 30000;
  /** True if Spaceship is towing GoalSphere. */
  private static boolean my_towed_state;
  /** The spaceship's current fuel. */
  private transient int my_fuel;

  /**
   * @return How much fuel do you contain?
   */
  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  public /*@ pure @*/ int fuel() {
    assert my_fuel <= MAX_FUEL : "Fuel is above maximum fuel.";
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int maximum_fuel() {
    return MAX_FUEL;
  }

  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
  }

  /**
   * @param the_fuel_change Change your fuel content by this many units.
   */
  /*@ ensures (\old(fuel() + the_fuel_change < 0) ?
    @            (fuel() == 0) :
    @          (\old(maximum_fuel() < (fuel() + the_fuel_change)) ?
    @             (fuel() == maximum_fuel()) :
    @           fuel() == \old(fuel() + the_fuel_change)));
    @*/
  public void change_fuel_content(final int the_fuel_change) {
    my_fuel += the_fuel_change;
  }

  //@ public invariant (* Fuel content is always non-negative and finite. *);
  //@ public invariant 0 <= fuel();

  //@ public invariant (* One unit of fuel weights 1kg. *);
  /**
   * @return What is the mass of your fuel?
   */
  //@ ensures \result == fuel * 1;
  public /*@ pure @*/ int fuel_mass() {
    return my_fuel;
  }

  /**
   * @return Are you currently towing or being towed?
   */
  public /*@ pure @*/ boolean towed() {
    return my_towed_state;
  }

  /**
   * You are now towing or being towed.
   */
  //@ ensures towed();
  public void tow() {
    my_towed_state = true;
  }

  //@ public initially_redundantly mass() == EMPTY_MASS + INITIAL_FUEL;

  /*@ public invariant (* The spaceship is destroyed by the barrier. *);
    @ public invariant (* The spaceship is destroyed by a bullet. *);
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
    @ public invariant (* The spaceship's color is always white. *);
    @ public invariant color() == thrust.entities.properites.GameColor.WHITE;
    @*/
}
