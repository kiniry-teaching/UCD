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
  /** The amount of fuel currently in the FuelPod. */
  private int my_fuel;
  /** The maximum amount of fuel that a FuelPod can hold. */
  private int my_max_fuel;
  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#change_fuel_content(int)
   */
  public void change_fuel_content(final int the_fuel_change) {
    if (my_fuel + the_fuel_change < 0) {
      my_fuel = 0;
    } else if (maximum_fuel() < (my_fuel + the_fuel_change)) {
      my_fuel = maximum_fuel();
    } else {
      my_fuel += the_fuel_change;
    }
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#fuel_mass()
   */
  public int fuel_mass() {
    return my_fuel;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#fuel()
   */
  public int fuel() {
    return my_fuel;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#maximum_fuel()
   */
  public int maximum_fuel() {
    return my_max_fuel;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.Fuelable#set_fuel_content(int)
   */
  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
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
