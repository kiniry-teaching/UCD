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
  public static final int INITIAL_FUEL = 1000;
  /**integer to set the fuel of the ship.*/
  private int my_fuel = INITIAL_FUEL;
  /**boolean to check tow state of ship.*/
  private boolean my_towness;
  /** integer myMaxi.*/
  private final int my_maxi = 100;
  /** integer for mass of fuel.*/
  private final int my_fuel_mass = 1;

  public final void changeFuelContent(final int the_fuel_change) {
    if (fuel() + the_fuel_change < 0) {
      my_fuel = 0;
    } else if (maxiumumFuel() < (fuel() + the_fuel_change)) {
      my_fuel = maxiumumFuel();
    } else {
      my_fuel = fuel() + the_fuel_change;
    }
  }

  //@ ensures \result == fuel * 1;
  public /*@ pure @*/ int fuel_mass()
  {
    return my_fuel * my_fuel_mass;
  }


  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  /*@ pure @*/
  public int fuel() {
    return my_fuel;
  }
  //@ ensures 0 <= \result;
  /*@ pure @*/
  public final int maxiumumFuel() {
    if (my_maxi >= 0) {
      return my_maxi;
    }
    return 0;
  }

//@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  public final void setFuelContent(final int the_fuel_content) {
    if (the_fuel_content >= 0 && the_fuel_content <= my_maxi) {
      my_fuel = the_fuel_content;
    }
  }

  public double mass() {
    return (EMPTY_MASS + my_fuel);
  }

  public void tow() {
    my_towness = true;
  }

  public boolean towed() {
    return my_towness;
  }

  public Color color() {
    return java.awt.Color.WHITE;
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
