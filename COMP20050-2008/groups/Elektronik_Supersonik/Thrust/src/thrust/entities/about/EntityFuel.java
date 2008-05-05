package thrust.entities.about;

/**
 * Enemy's AI.
 * @author Elektronik Supersonik (.@.)
 * @version 05 May 2008
 */
public class EntityFuel implements Fuelable {
  /**
   * The maximum amount of fuel the entity can have.
   */
  private static final int MAX_FUEL = 1000;
  /**
   * The mass of a unit of fuel.
   */
  private static final int FUEL_UNIT_MASS = 1;
  /**
   * The fuel an entity has.
   */
  private transient int my_fuel;

  public EntityFuel(final int the_initial_fuel) {
    my_fuel = the_initial_fuel;
  }

  public void change_fuel_content(final int the_fuel_change) {
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

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel = the_fuel_content;
  }
}
