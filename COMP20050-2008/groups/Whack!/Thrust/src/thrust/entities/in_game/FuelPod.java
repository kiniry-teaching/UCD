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

import thrust.animation.AnimatableWhack;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.entities.about.Fuelable;
import thrust.entities.about.FuelableWhack;


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
  FuelableWhack my_fuel;
  /**
   *
   */
  Color my_fuelpodcolor;
  /**
   *
   */
  Shape my_fuelpodshape;
  /**
   *
   */
  AnimatableWhack my_animation;
  /**
   *
   */
  double my_speed;
  /**
   *
   */
  double my_anglerad;
  /**
   *
   */
  double my_mass;
  /**
   *
   */
  double[] my_position;
  /**
   *
   */
  double my_orientation;
  /**
   *
   */
  double[] my_acceleration;
  /**
   *
   */
  double[] my_velocity;
  /**
   *
   */
  String my_shapename;
  /**
   *
   */
  StaticEntity my_ent;

  public double[] acceleration() {

    return my_ent.acceleration();
  }

  public void acceleration(final double[] the_acceleration) {
    my_ent.acceleration(the_acceleration);
  }
  public void simulate(final double a_time_interval) {
    // TODO Auto-generated method stub

  }

  public double mass() {

    return my_mass;

  }
  public void mass(final double the_mass) {
    my_ent.mass(the_mass);
  }


  public double momentum() {

    final int my_elements = 2;
    double[] my_s = new double[my_elements];
    my_s = velocity();

    return mass() * my_s[0];

  }
  public void orientation(final double the_orientation) {

    my_ent.orientation(the_orientation);

  }
  public double orientation() {

    return my_orientation;

  }
  public double[] velocity() {

    final int my_elements = 2;
    final double[] my_vel = new double[my_elements];
    my_vel[0] = my_speed;
    my_vel[1] = orientation();
    return my_vel;

  }
  public void velocity(final double[] the_velocity) {
    my_ent.velocity(the_velocity);
  }
  public double gravitational_constant() {
    return my_ent.gravitational_constant();
  }
  public double[] position() {
    return my_position;
  }

  public void position(final double[] the_position) {
    my_ent.position(the_position);
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
    int my_width = 1;
    /**
     * height of rectangle.
     */
    int my_height = 1;
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

    final String my_name = "Fuel Box";
    return my_name;

  }

  public byte state() {

    return 0;

  }

  public void state(final byte the_state) {


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
