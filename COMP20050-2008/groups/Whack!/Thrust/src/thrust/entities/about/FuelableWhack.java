package thrust.entities.about;
/**
 * @author David Maguire (David.Maguire.2@ucdconnect.ie)
 * @version 11 April 2008
 */
public class FuelableWhack implements Fuelable {

  /**the fuel.*/
  int my_fuel;
  /**maximum fuel.*/
  final int my_maxFuel = 9999;

  public FuelableWhack(final int the_startfuel) {
    my_fuel = the_startfuel;
  }
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

    return my_maxFuel;
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
    }

    if (my_fuel + the_fuel_change > maximum_fuel()) {
      my_fuel = maximum_fuel();
    }

    my_fuel = my_fuel + the_fuel_change;

    //@ invariant (* Fuel content is always non-negative and finite. *);
    //@ invariant 0 <= fuel();
  }
  public int fuel_mass() {
    return fuel() * 1;

  }
}


