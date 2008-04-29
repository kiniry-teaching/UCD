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
  public static final int INITIAL_FUEL = 1000;

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
