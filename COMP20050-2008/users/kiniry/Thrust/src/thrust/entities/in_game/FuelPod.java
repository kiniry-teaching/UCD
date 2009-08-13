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
import thrust.entities.about.Fuelable;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class FuelPod extends StaticEntity
  implements NeutralEntity, Fuelable {
  /** The initial amount of fuel in each small fuel pod. */
  private static final int INITIAL_SMALL_FUEL_POD_FUEL_CONTENT = 250;

  /** The initial amount of fuel in each medium fuel pod. */
  private static final int INITIAL_MEDIUM_FUEL_POD_FUEL_CONTENT = 300;

  /** The initial amount of fuel in each large fuel pod. */
  private static final int INITIAL_LARGE_FUEL_POD_FUEL_CONTENT = 350;

  /** The three sizes of fuel pods. */
  private static final int SMALL_POD = 0, MEDIUM_POD = 1, LARGE_POD = 2;

  /** The current fuel content of this fuel pod. */
  private transient int my_fuel_content;
  //@ invariant 0 <= my_fuel_content;

  /**
   * Create a new fuel pod in one of three sizes.
   * @param the_size the size of this new fuel pod, either
   * SMALL, MEDIUM, or LARGE.
   */
  /*@ requires the_size == SMALL_POD |
    @          the_size == MEDIUM_POD |
    @          the_size == LARGE_POD;
    @*/
  public FuelPod(final byte the_size) {
    super();
    switch (the_size) {
      case SMALL_POD:
        my_fuel_content = INITIAL_SMALL_FUEL_POD_FUEL_CONTENT;
        break;
      case MEDIUM_POD:
        my_fuel_content = INITIAL_MEDIUM_FUEL_POD_FUEL_CONTENT;
        break;
      case LARGE_POD:
        my_fuel_content = INITIAL_LARGE_FUEL_POD_FUEL_CONTENT;
        break;
      default: assert false; //@ assert false;
    }
  }

  public void change_fuel_content(final int the_fuel_change) {
    my_fuel_content += the_fuel_change;
  }

  public int fuel() {
    return my_fuel_content;
  }

  public int fuel_mass() {
    return my_fuel_content * MASS_PER_UNIT;
  }

  public int maximum_fuel() {
    return INITIAL_LARGE_FUEL_POD_FUEL_CONTENT;
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel_content = the_fuel_content;
  }

  /*@ public invariant (* A fuel pod is destroyed by a bullet. *);
    @ public invariant (* The fuel pod is not affected by the goal sphere. *);
    @ public invariant (* The fuel pod is not affected by the spaceship. *);
    @ public invariant (* A fuel pod's color is always yellow. *);
    @ public invariant color() == java.awt.Color.YELLOW;
    @ public invariant (* A fuel pod's 'fuel' lettering color is
    @                     dictated by the amount of fuel it contains. *);
    @*/
}
