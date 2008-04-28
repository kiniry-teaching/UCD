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

  /** Int holding maximum amount of fuel in the Fuelpod. */
  private static final int MY_MAXFUEL = 500;
  /** Int holding current amount of fuel in the Fuelpod. */
  private static int my_fuel;
  /** Int holding mass of fuel. */
  private static int my_fuel_mass = my_fuel;

  /**
   * @return How much fuel do you contain?
   */
  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  public /*@ pure @*/ int fuel() {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int maximum_fuel() {
    return MY_MAXFUEL;
  }
  
  //@ public invariant (* One unit of fuel weights 1kg. *);
  /**
   * @return What is the mass of your fuel?
   */
  //@ ensures \result == fuel * 1;
  public /*@ pure @*/ int fuel_mass() {
    return my_fuel_mass;
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
    my_fuel += the_fuel_change; // Clumsy, fix in future.
  }

  //@ public invariant (* Fuel content is always non-negative and finite. *);
  //@ public invariant 0 <= fuel();



  /*@ public invariant (* A fuel pod is destroyed by a bullet. *);
    @ public invariant (* The fuel pod is not affected by the goal sphere. *);
    @ public invariant (* The fuel pod is not affected by the spaceship. *);
    @ public invariant (* A fuel pod's color is always yellow. *);
    @ public invariant color() == thrust.entities.properties.GameColor.YELLOW;
    @ public invariant (* A fuel pod's 'fuel' lettering color is
    @                     dictated by the amount of fuel it contains. *);
    @*/
}
