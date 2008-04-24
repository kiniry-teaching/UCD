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
    @ public invariant (* The spaceship's colour is always white. *);
    @ public invariant colour() == thrust.entities.properites.GameColor.WHITE;
    @*/
}
