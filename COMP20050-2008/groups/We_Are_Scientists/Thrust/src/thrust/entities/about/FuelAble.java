package thrust.entities.about;

/**
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * Original by Simon Markey.
 * @version 11 April 2008
 */
public class FuelAble implements Fuelable {

  /** The integer value that is the fuel. */
  private transient float my_fuel;

  /** maximum fuel available. */
  private final transient float my_max_fuel = Float.POSITIVE_INFINITY;

  public FuelAble(final float the_initial_fuel) {
    my_fuel = the_initial_fuel;
  }

  /**
   * @return How much fuel do you contain?
   */
  // @ ensures 0 <= \result;
  // @ ensures \result <= maximum_fuel();
  public/* @ pure @ */float fuel() {
    return my_fuel;
  }

  /**
   * @return How much fuel can you contain?
   */
  // @ ensures 0 <= \result;
  public/* @ pure @ */float maximum_fuel() {

    return my_max_fuel;
  }

  /**
   * @param the_fuel_content
   *          This many units is your fuel content.
   */
  // @ requires 0 <= the_fuel_content & the_fuel_content <= maximum_fuel();
  // @ ensures fuel() == the_fuel_content;
  public void set_fuel_content(final float the_fuel_content) {

    if (the_fuel_content >= 0 && the_fuel_content <= maximum_fuel()) {
      my_fuel = the_fuel_content;
    }
  }

  /**
   * @param fuel_difference
   *          Change your fuel content by this many units.
   */
  /*
   * @ ensures (\old(fuel() + the_fuel_change < 0) ? @ (fuel() == 0) : @
   * (\old(maximum_fuel() < (fuel() + the_fuel_change)) ? @ (fuel() ==
   * maximum_fuel()) : @ fuel() == \old(fuel() + the_fuel_change))); @
   */
  public void change_fuel_content(final float the_fuel_difference) {

    if (my_fuel + the_fuel_difference < 0) {
      my_fuel = 0;
    }

    if (my_fuel + the_fuel_difference > my_max_fuel) {
      my_fuel = my_max_fuel;
    }

    my_fuel = my_fuel + the_fuel_difference;

    // @ invariant (* Fuel content is always non-negative and finite. *);
    // @ invariant 0 <= fuel();
  }

  public float fuel_mass() {
    float answer;
    if (my_fuel < 0) {
      answer = fuel() * -1;
    } else {
      answer = my_fuel * 1;
    }
    return answer;

  }

}
