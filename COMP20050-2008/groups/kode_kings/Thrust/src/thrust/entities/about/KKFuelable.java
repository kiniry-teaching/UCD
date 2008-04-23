/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Colin Casey (colin.casey@org.com)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.about;

/**
 * @author Colin Casey (colin.casey@org.com)
 * @version 23 April 2008
 */
public class KKFuelable implements Fuelable {

  /** The maximum amount of fuel that can be contained. */
  private static final int MAX_FUEL = 10000;
  /** The amount of fuel that is contained. */
  private static int my_fuel;

  public int fuel() {
    return my_fuel;
  }

  public int maximum_fuel() {
    return MAX_FUEL;
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
  }

  public void change_fuel_content(final int the_fuel_change) {
    my_fuel = my_fuel + the_fuel_change;
  }

  public int fuel_mass() {
    return my_fuel;
  }
}
