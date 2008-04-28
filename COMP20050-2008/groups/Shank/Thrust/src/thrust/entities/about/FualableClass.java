package thrust.entities.about;
/**
 * @author Ben Fitzgerald (ben.fitz@hotmail.com)
 * @version 28 April 2008
 * */
public  class FualableClass implements Fuelable {

  /**The amount fuel.*/
  private int my_fuel;
  /**The fuel mass.*/
  private int my_fuel_mass;
  /**The fuel amount of content.*/
  private int my_fuel_content;
  /**The maximum amount of fuel.*/
  private final int my_fuel_maximum = 10000;
  /**
   * @return This many units is your fuel content.
   * */
  public int fuel() {
    my_fuel_mass = fuel() * 1;
    return my_fuel;
  }
  /**
   * @return The mass of the fuel content.
   * */
  public int fuel_mass() {
    return my_fuel_mass;
  }
  /**
   * @return The maximum amount of fuel .
   * */
  public int maximum_fuel() {
    return my_fuel_maximum;
  }
  /**
   * @param Sets the amount of fuel content.
   * */
  public void set_fuel_content(final int the_fuel_content) {
    my_fuel_content = the_fuel_content;
  }
  /**
   * @param Sets the amount of fuel content that change.
   * */
  public void change_fuel_content(final int the_fuel_change) {
    my_fuel_content   = the_fuel_change;
  }
}
