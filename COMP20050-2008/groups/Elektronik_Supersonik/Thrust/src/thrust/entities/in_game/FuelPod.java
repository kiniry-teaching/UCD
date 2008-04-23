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

import java.awt.Shape;

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.EntityFuel;
import thrust.entities.about.Fuelable;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class FuelPod extends StaticEntity implements NeutralEntity, Fuelable {
  /**
   * The fuel of the Pod.
   */
  private EntityFuel my_fuel;

  public FuelPod(final String the_initial_shape_name, final Shape the_initial_shape,
      final byte the_initial_state, final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass, final double[] the_velocity) {
    super();
    super.set_state(the_position, the_orientation, the_acceleration, the_mass,
                    the_velocity, the_initial_shape_name, the_initial_shape,
                    the_initial_state);
  }

  public void change_fuel_content(final int the_fuel_change) {
    my_fuel.change_fuel_content(the_fuel_change);
  }

  public int fuel() {
    return my_fuel.fuel();
  }

  public int fuel_mass() {
    return my_fuel.fuel_mass();
  }

  public int maximum_fuel() {
    return my_fuel.fuel();
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel.set_fuel_content(the_fuel_content);
  }

  /*@ public invariant (* A fuel pod is destroyed by a bullet. *);
    @ public invariant (* The fuel pod is not affected by the goal sphere. *);
    @ public invariant (* The fuel pod is not affected by the spaceship. *);
    @ public invariant (* A fuel pod's color is always yellow. *);
    @ public invariant color() == java.awt.Color.YELLOW;
    @ public invariant (* A fuel pod's 'fuel' lettering color is
    @                     dictated by the amount of fuel it contains. *);
    @*/
}
