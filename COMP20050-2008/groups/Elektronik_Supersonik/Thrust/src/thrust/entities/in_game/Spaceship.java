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

import java.awt.Shape;

import thrust.entities.DynamicEntity;
import thrust.entities.FriendEntity;
import thrust.entities.about.EntityFuel;
import thrust.entities.about.Fuelable;
import thrust.entities.behaviors.Tow;

/**
 * The player's main vehicle.
 * @author Elektronik Supersonik (.@.)
 * @version 18 April 2008
 */
public class Spaceship extends DynamicEntity implements FriendEntity, Fuelable,
    Tow {
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
  /**
   * The fuel of the Spaceship.
   */
  private transient EntityFuel my_fuel;
  /**
   * Am i towing?
   */
  private transient boolean my_towing;

  public Spaceship(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_initial_shape_name,
      final Shape the_initial_shape, final byte the_initial_state) {

    super();
    super.set_dynamic_state(the_position, the_orientation, the_acceleration,
                            the_mass, the_velocity, the_initial_shape_name,
                            the_initial_shape, the_initial_state);
    my_fuel = new EntityFuel(INITIAL_FUEL);
  }

  public void change_fuel_content(final int the_fuel_change) {
    my_fuel.change_fuel_content(the_fuel_change);
  }

  public int fuel() {
    return my_fuel.fuel();
  }

  public int fuel_mass() {
    return my_fuel.fuel_mass();
  }

  public int maximum_fuel() {
    return my_fuel.fuel();
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel.set_fuel_content(the_fuel_content);
  }

  public void tow() {
    my_towing = true;
  }

  public boolean towed() {
    return my_towing;
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
