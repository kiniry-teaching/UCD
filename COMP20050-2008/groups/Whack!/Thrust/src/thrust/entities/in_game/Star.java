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
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;


/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
    implements NeutralEntity, Animatable {
  /**
   *
   * @author Allison Fallon(allison.fallon@ucdconnect.ie)
   *@version 23 April 2008
   */
  Color my_starcolor;
  /**
   *
   */
  Shape my_starshape;
  /**
   *
   */
  final double my_speed;
  /**
   *
   */
  final double my_anglerad;
  /**
   *
   */
  final double my_mass;

  public double[] acceleration() {

    return null;
  }

  public double mass() {

    return my_mass;

  }

  public double momentum() {

    final int my_elements = 2;
    final double[] my_s = new double[my_elements];
    my_s = velocity();

    return mass() * my_s[0];

  }
  public void orientation(final double the_angle) {

    my_anglerad = the_angle;

  }
  public double orientation() {

    return my_anglerad;

  }
  public double[] velocity() {

    final int my_elements = 2;
    final double[] my_vel = new double[my_elements];
    my_vel[0] = my_speed;
    my_vel[1] = orientation();
    return my_vel;

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
    final Rectangle my_a = new Rectangle(10, 10);

    my_starshape = (Shape)my_a;

    return my_starshape;

  }

  public void shape(final Shape the_shape) {

    my_starshape = the_shape;

  }

  public String shape_name() {
    final String my_name = "Square";
    return my_name;
  }

  public byte state() {

    return 0;
  }

  public void state(final byte the_state) {


  }

  public void animate() {


  }

  public Animation animation() {

    return null;
  }

  public void animation(final Animation the_animation) {


  }
  public Color color() {

    my_starcolor.equals(Color.DARK_GRAY);
    my_starcolor.equals(Color.LIGHT_GRAY);

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

