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
  Color my_fuelpodcolor;
  /**
   *
   */
  Shape my_fuelpodshape;

  public double[] acceleration() {

    return null;
  }

  public double mass() {

    return 0;
  }

  public double momentum() {

    return 0;
  }

  public double[] velocity() {

    return null;
  }

  public void render() {


  }

  /**
   *
   */
  public class Point {
    /**
     *
     */
    int my_rx = 1;
    /**
     *
     */
    int my_ry = 1;

    public Point(final int the_rx, final int the_ry) {

      my_rx = the_rx;
      my_ry = the_ry;

    }

  }
  /**
   *
   */
  public class Rectangle {
    /**
     * width of rectangle.
     */
    final int my_width = 0;
    /**
     * height of rectangle.
     */
    final int my_height = 0;
    /**
     *
     */
    final Point my_org;

    public Rectangle() {

      my_org = new Point(0, 0);

    }

    public Rectangle(final Point the_p) {

      my_org = the_p;

    }
    public Rectangle(final int the_w, final int the_h) {

      my_org = new Point(0, 0);
      my_width = the_w;
      my_height = the_h;

    }
    public Rectangle(final Point the_p, final int the_w, final int the_h) {

      my_org = the_p;
      my_width = the_w;
      my_height = the_h;

    }

  }

  public Shape shape() {
    /**
     *
     */
    final Rectangle my_a = new Rectangle(10, 40);

    my_fuelpodshape = (Shape)my_a;

    return my_fuelpodshape;

  }

  public void shape(final Shape the_shape) {

    my_fuelpodshape = the_shape;

  }


  public String shape_name() {

    return null;

  }

  public byte state() {

    return 0;

  }

  public void state(final byte the_state) {


  }

  public void change_fuel_content(final int the_fuel_change) {


  }

  public int fuel() {

    return 0;

  }

  public int fuel_mass() {

    return 0;

  }

  public int maximum_fuel() {

    return 0;

  }

  public void set_fuel_content(final int the_fuel_content) {


  }

  public Color color() {
    my_fuelpodcolor.equals(Color.YELLOW);
    return my_fuelpodcolor;
  }

  public void color(final Color the_color) {

    my_fuelpodcolor = the_color;
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
