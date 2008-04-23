package thrust.entities.about;

public class EntityFuel implements Fuelable {
  /**
   * The fuel an entity has.
   */
  private int my_fuel;
  /**
   * The maximum amount of fuel the entity can have.
   */
  private static final int MAX_FUEL = 1000;
  /**
   * The mass of a unit of fuel.
   */
  private static final int FUEL_UNIT_MASS = 1;
  
  public EntityFuel(final int the_initial_fuel) {
     my_fuel = the_initial_fuel;
  }

  public void change_fuel_content(int the_fuel_change) {
    my_fuel += the_fuel_change;
  }

  public int fuel() {
    return my_fuel;
  }

  public int fuel_mass() {
    return my_fuel * FUEL_UNIT_MASS;
  }

  public int maximum_fuel() {
    return MAX_FUEL;
  }

  public void set_fuel_content(int the_fuel_content) {
    my_fuel = the_fuel_content;
  }
  
  
}
