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
import java.awt.Color;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.Fuelable;
import thrust.entities.about.FuelableClass;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Eoin Healy (eoin.healy@gmail.com)
 * @version 18 April 2008
 */
public class FuelPod extends StaticEntity
  implements NeutralEntity, Fuelable {
/**
* The color of entity.
*/
  private Color my_color = Color.YELLOW;
/**
 * The fuel.
 */
  private FuelableClass my_fuel;
/**
*
* @param the_position
* @param the_orientation
* @param the_initial_shape_name
* @param the_initial_shape
* @param the_inital_state
*/

  public FuelPod(final double[] the_position,
                       final double the_orientation,
                       final String the_initial_shape_name,
                       final Shape the_initial_shape,
                       final byte the_inital_state) {
    super.set_state(the_position, the_orientation,
                    my_color, the_initial_shape_name,
                    the_initial_shape, the_inital_state);
  }
  /*@ public invariant (* A fuel pod is destroyed by a bullet. *);
    @ public invariant (* The fuel pod is not affected by the goal sphere. *);
    @ public invariant (* The fuel pod is not affected by the spaceship. *);
    @ public invariant (* A fuel pod's color is always yellow. *);
    @ public invariant color() == thrust.entities.properties.GameColor.YELLOW;
    @ public invariant (* A fuel pod's 'fuel' lettering color is
    @                     dictated by the amount of fuel it contains. *);
    @*/

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
    return my_fuel.maximum_fuel();
  }

  public void set_fuel_content(final int the_fuel_content) {
    my_fuel.set_fuel_content(the_fuel_content);
  }
}
