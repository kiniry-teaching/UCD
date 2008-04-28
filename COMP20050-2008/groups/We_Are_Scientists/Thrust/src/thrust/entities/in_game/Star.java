/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Simon markey (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Color;
import java.awt.Shape;
import thrust.animation.Animatable;
import thrust.animation.Animation_class;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import javax.swing.Timer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity implements NeutralEntity, Animatable {
  /**
   *
   * @author Allison Fallon(allison.fallon@ucdconnect.ie)
   *@version 23 April 2008
   */
  Animation_class my_animation;
  /**
   *
   */
 final double my_speed =0;
  /**
   *
   */
 double my_anglerad =0;
  /**
   *
   */
  final double my_mass=0;
  /**
   *
   */
   byte my_state;
  /**
   *
   */
  Color my_starcolor=Color.WHITE;
  /**
   *
   */
  Shape my_starshape;

  /**
   *
   */

  public double[] acceleration() {

    return null;
  }

  public double mass() {

    return my_mass;

  }

  public double momentum() {

    final int my_elements = 2;
    double[] my_s = new double[my_elements];
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
    final double[] my_velocity = new double[my_elements];
    my_velocity[0] = my_speed;
    my_velocity[1] = orientation();
    return my_velocity;

  }

  
  
  /*
    if(elapsed==10)
    {animate();}
  long timeBefore = System.currentTimeMillis();
  long timeAfter = System.currentTimeMillis();
  long elapsed = timeAfter - timeBefore;
  System.out.println("Elapsed time in milliseconds: " + elapsed);
   * 
   * 
   */
  
  
  /**
   *
   */
 

  public void render() {
    
  long time = System.currentTimeMillis();
  //long timeAfter = System.currentTimeMillis();
  //long elapsed = timeAfter - timeBefore;
  if(time%10==0)
  {
    //not quite sure if this should be animate();????
    my_starcolor.equals(Color.LIGHT_GRAY);
  }
  
  
  //System.out.println("Elapsed time in milliseconds: " + elapsed);

  }

  /**
   *
   */
  public class Point {
    /**
     *
     */
    int my_x = (int) Math.random();
    /**
     *
     */
    int my_y = (int) Math.random();

    public Point(final int the_x, final int the_y) {

      my_x = the_x;
      my_y = the_y;

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
    final Point my_origin;

    public Rectangle() {

      my_origin = new Point(0, 0);

    }

    public Rectangle(final Point the_p) {

      my_origin = the_p;

    }

    public Rectangle(final int the_w, final int the_h) {

      my_origin = new Point(0, 0);
      my_width = the_w;
      my_height = the_h;

    }

    public Rectangle(final Point the_p, final int the_w, final int the_h) {

      my_origin = the_p;
      my_width = the_w;
      my_height = the_h;

    }
  }

  public Shape shape() {
    /**
     *
     */
    final Rectangle my_a = new Rectangle(1, 1);

    my_starshape = (Shape) my_a;

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

    my_starcolor.equals(Color.GRAY);

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