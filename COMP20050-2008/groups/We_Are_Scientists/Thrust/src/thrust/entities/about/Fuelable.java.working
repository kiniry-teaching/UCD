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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 11 April 2008
 */



public class Fuelable {
  /**
   * @return How much fuel do you contain?
   */
  //@ ensures 0 <= \result;
  //@ ensures \result <= maximum_fuel();
  /*@ pure @*/

  /**
   * @return your fuel
   */
  int my_fuel;
  int fuel()
  {

    my_fuel = maximum_fuel();
    return my_fuel;


  }

  /**
   * @return How much fuel can you contain?
   */
  //@ ensures 0 <= \result;
  /*@ pure @*/ int maximum_fuel()
  {
    final int maximum_fuel = 9999;
    return maximum_fuel;
  }
  /**
   * @param the_fuel_content This many units is your fuel content.
   */
  //@ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  //@ ensures fuel() == the_fuel_content;
  void set_fuel_content(final int the_fuel_content)
  {
    if (the_fuel_content >= 0 && the_fuel_content <= maximum_fuel())
    {
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
  void change_fuel_content(final int the_fuel_change)
  {
    if (my_fuel + the_fuel_change < 0)
    {
      my_fuel = 0;
    }

    if (my_fuel + the_fuel_change > maximum_fuel())
    {
      my_fuel = maximum_fuel();
    }

    my_fuel = my_fuel + the_fuel_change;

  }

  //@ invariant (* Fuel content is always non-negative and finite. *);
  //@ invariant 0 <= fuel();
}
