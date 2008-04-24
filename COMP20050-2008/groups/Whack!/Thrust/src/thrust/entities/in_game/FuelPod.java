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
import thrust.entities.about.Fuelable;

/**
 * A fuel pod from which the spaceship can obtain fuel.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class FuelPod extends StaticEntity
    implements NeutralEntity, Fuelable {
  /**
   * @author allison fallon(allison.fallon@ucdconnect.ie)
   */

  public double[] acceleration() {
    // TODO Auto-generated method stub
    return null;
  }

  public double mass() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double momentum() {
    // TODO Auto-generated method stub
    return 0;
  }

  public double[] velocity() {
    // TODO Auto-generated method stub
    return null;
  }

  public void render() {
    // TODO Auto-generated method stub

  }

  public Shape shape() {
    // TODO Auto-generated method stub
    return null;
  }

  public void shape(final Shape the_shape) {
    // TODO Auto-generated method stub

  }

  public String shape_name() {
    // TODO Auto-generated method stub
    return null;
  }

  public byte state() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void state(final byte the_state) {
    // TODO Auto-generated method stub

  }

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

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO Auto-generated method stub
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
