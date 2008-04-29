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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.Fuelable;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Kevin Lambe (kevlambe@gmail.com)
 * @version 25 April 2008
 */
public class FuelPod extends StaticEntity
  implements NeutralEntity, Fuelable {
  /**
   * The mass of the fuelpod.
   */
  private Fuelable my_mass;
  /**
   * Color of the fuel pod.
   */
  private Color my_color;

  /**
   * int representing fuel content.
   */
  private int my_fuel_content;
  /**
   * the maximum fuel content.
   */
  private int my_maximum_fuel;

  public Fuelable mass(final Fuelable the_mass)
  {
    my_mass = the_mass;
    return my_mass;
  }

  public int fuel_mass()
  {
    return my_fuel_content;
  }

  public void color(final Color the_color) {
    my_color = the_color;
  }
  public Color color() {
    return my_color;
  }

  public void change_fuel_content(final int the_fuel_change)
  {
    my_fuel_content = my_fuel_content - the_fuel_change;
  }

  public void set_fuel_content(final int the_fuel_content)
  {
    my_fuel_content = the_fuel_content;
  }
  public int fuel() {
    return my_fuel_content;
  }
  public int maximum_fuel() {
    return my_maximum_fuel;
  }
  public void simulate(final double the_amount) {
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
