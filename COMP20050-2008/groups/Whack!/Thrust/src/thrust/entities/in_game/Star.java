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
import thrust.animation.Animatable;
import thrust.animation.AnimatableWhack;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import javax.swing.Timer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import thrust.physics.PhysicsInterface;


/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
    implements NeutralEntity, Animatable, PhysicsInterface {
  /**
   *
   *@author Allison Fallon(allison.fallon@ucdconnect.ie)
   *@edited Tara Flood (Tara.Flood@ucdconnet.ie)
   *@version 23 April 2008
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
  byte my_state;
  /**
   *
   */
  Color my_starcolor;
  /**
   *
   */
  Shape my_starshape;
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

    my_ent.simulate(a_time_interval);

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
  public double orientation() {

    return my_orientation;

  }

  public void orientation(final double the_orientation) {

    my_ent.orientation(the_orientation);

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
    return  my_position;
  }

  public void position(final double[] the_position) {
    my_ent.position(the_position);
  }
  /**
   *
   */
  class Listener implements ActionListener {
    public void actionPerformed(final ActionEvent the_event) {
      my_starcolor.equals(Color.LIGHT_GRAY);
    }
  }

  public void render() {
    final Listener my_listener = new Listener();
    final Timer my_timer = new Timer(500, my_listener);
    my_timer.start();

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
    final Rectangle my_a = new Rectangle(2, 2);

    my_starshape = (Shape)my_a;

    return my_starshape;

  }

  public void shape(final Shape the_shape) {

    my_starshape = the_shape;

  }

  public String shape_name() {
    final String my_name = "Star";
    return my_name;
  }
  public byte state() {

    return my_state;
  }
  /**
   *
   * @param the_position
   * @param the_orientation
   * @param the_acceleration
   * @param the_mass
   * @param the_velocity
   * @param the_shapename
   * @param the_shape
   * @param the_state
   */
  public void set_state(final byte the_state) {


  }

  public void animate() {
    my_animation.animate();

  }

  public Animation animation() {

    return my_animation.animation();
  }

  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);

  }
  public Color color() {

    my_starcolor.equals(Color.DARK_GRAY);


    return my_starcolor;

  }

  public void color(final Color the_color) {


    my_starcolor = the_color;

  }



}
/*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/

