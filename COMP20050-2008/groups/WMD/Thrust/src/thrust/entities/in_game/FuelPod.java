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

import java.awt.Color;
import java.awt.Shape;

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.FuelableInterface;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 1 May 2008
 */
public class FuelPod extends StaticEntity
  implements  FuelableInterface, NeutralEntity {

  /**
   * The color of a fuel pod.
   */
  Color my_color;

  /**
   * Make a fuel pod.
   */
  public FuelPod(final double[] a_position,
                 final double an_orientation,
                 final double a_mass,
                 final double[] a_velocity,
                 final String an_initial_shape_name,
                 final Shape an_initial_shape,
                 final byte an_initial_state) {

    super();
    color(Color.YELLOW);
    super.set_Staticstate(a_position, an_orientation, null,
                          a_mass, a_velocity, an_initial_shape_name,
                          an_initial_shape, an_initial_state);

  }


  public Color color() {
    return my_color;
  }

  public void color(final Color the_color) {
    my_color = the_color;
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
    // TODO Auto-generated method stub
  }

  public int fuel() {
    // TODO Auto-generated method stub
    return 0;
  }

  public int fuel_mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public int maximum_fuel() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void set_fuel_content(final int the_fuel_content) {
    // TODO Auto-generated method stub
  }
}
