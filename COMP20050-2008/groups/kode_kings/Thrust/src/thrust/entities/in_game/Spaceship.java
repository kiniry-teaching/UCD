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
 * @author Colin Casey (colin.casey@org.com)
 * @version 23 April 2008
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
  /** The maximum amount of fuel that can be contained. */
  private static final int MAX_FUEL = 10000;
  /** The amount of fuel that is contained. */
  private static int my_fuel;
  /** Tow status of Spaceship. */
  private boolean my_tow_indicator;

  public boolean towed() {
    return my_tow_indicator;
  }

  public void tow() {
    my_tow_indicator = true;
  }

  public int fuel() {
    return my_fuel;
  }

  public int maximum_fuel() {
    return MAX_FUEL;
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
  }

  public void change_fuel_content(final int the_fuel_change) {
    my_fuel = my_fuel + the_fuel_change;
  }

  public int fuel_mass() {
    return my_fuel;
  }

  //@ public initially mass() == EMPTY_MASS + INITIAL_FUEL;

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
    @ public invariant mass() == EMPTY_MASS + fuel_mass() +
    @                  (towed() ? GoalSphere.MASS : 0);
    @ public invariant (* The spaceship's shape is always that of a ship. *);
    @ public invariant (* The spaceship's color is always white. *);
    @ public invariant color() == java.awt.Color.WHITE;
    @*/
}
