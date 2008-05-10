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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.Fuelable;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * Original by Simon.
 * @version 10 May 2008
 */
public class FuelPod extends StaticEntity
  implements NeutralEntity, Fuelable {

  /** The integer value that is the fuel. */
  private transient int my_fuel;

  /** maximum fuel available. */
  private final transient int my_max_fuel = (int) Float.POSITIVE_INFINITY;

  /**
  *
  * @param the_position
  * @param the_orientation
  * @param the_acceleration
  * @param the_mass
  * @param the_velocity
  * @param the_initial_shape_name
  * @param the_initial_shape
  * @param the_initial_state
  */

  /**
   * @return How much fuel do you contain?
   */
  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  public int fuel() {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  public int maximum_fuel() {
    return my_max_fuel;
  }

  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  public void set_fuel_content(final int the_fuel_content) {
    if (the_fuel_content >= 0 && the_fuel_content <= maximum_fuel()) {
      my_fuel = the_fuel_content;
    }
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
    if (my_fuel + the_fuel_change < 0) {
      my_fuel = 0;
    } else if (my_fuel + the_fuel_change > my_max_fuel) {
      my_fuel = my_max_fuel;
    } else {
      my_fuel = my_fuel + the_fuel_change;
    }
    // @ invariant (* Fuel content is always non-negative and finite. *);
    // @ invariant 0 <= fuel();
  }

  //@ public invariant (* Fuel content is always non-negative and finite. *);
  //@ public invariant 0 <= fuel();

  //@ public invariant (* One unit of fuel weights 1kg. *);
  /**
   * @return What is the mass of your fuel?
   */
  //@ ensures \result == fuel() * 1;
  public int fuel_mass() {
    //Assume each unit of fuel has mass 1.
    return my_fuel;
  }

  public Color color() {
    return java.awt.Color.YELLOW;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.YELLOW) {
      my_Color(java.awt.Color.YELLOW);
    }
  }
}
