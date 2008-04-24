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
 * Abstract class implemented by the Fuelable interface.
 * @author jdouglas (jd2088@gmail.com)
 * @version 7 April 2008
 */
public class FuelableClass implements Fuelable {
/**
* The amount of fuel that is contained.
*/
  private int my_fuel;
/**
* The mass of the fuel.
*/
  private int my_fuel_mass;
  /**
* The change in the fuel content by a specific amount of units.
*/
  private int my_fuel_content;
//@ ensures 0 <= \result;
//@ ensures \result <= maximum_fuel();
/*@ pure @*/
  public int fuel() {
    return my_fuel;
  }
/**
 * returns the maximum amount of fuel that can you contain?
 */
//@ ensures 0 <= \result;
/*@ pure @*/
  public int maximum_fuel() {
    final int an_max_fuel = 9999;
    return an_max_fuel;
  }
  /**
   * @return What is the mass of your fuel?
   */
  //@ ensures \result == fuel() * 1;
  public /*@ pure @*/ int fuel_mass() {
    my_fuel_mass = fuel() * 1;
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
//@ invariant (* Fuel content is always non-negative and finite. *);
//@ invariant 0 <= fuel()
  public void change_fuel_content(final int the_fuel_change) {
    my_fuel_content = the_fuel_change;
  }
}
