/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.about;

/**
 * Implementation of Fuelable interface.
 * @author Magdalena Zieniewicz (mazienie@gmail.com)
 * @version 24 April 2008
 */
public class FuelableClass implements Fuelable {
  
  /** Volume of fuel in the tank in liters. */
  private int my_fuel;
  /** Capacity of fuel tank. */
  private int my_max_fuel;
  
  public FuelableClass(int the_initial_fuel, int the_max_fuel){
    my_fuel = the_initial_fuel;
    my_max_fuel = the_max_fuel;
    
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


  //@ public invariant (* Fuel content is always non-negative and finite. *);
  //@ public invariant 0 <= fuel();

  //@ public invariant (* One unit of fuel weights 1kg. *);

  public void change_fuel_content(int the_fuel_change) {
   int fuel = fuel() + the_fuel_change;
   my_fuel = fuel;
  }

  /**
   * @return How much fuel do you contain?
   */
  public int fuel() {
    return my_fuel;
  }

  /**
   * @return What is the mass of your fuel?
   */
  public int fuel_mass() {
    return fuel() * 1;
  }

  /**
   * @return How much fuel can you contain?
   */
  public int maximum_fuel() {
    return my_max_fuel;
  }

  
  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  public void set_fuel_content(int the_fuel_content) {
   my_fuel = the_fuel_content;
  }

}
