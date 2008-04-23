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
  /**
   *
   * @author allison
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
   * @author allison
   *
   */
  public class Rectangle {
    /**
     *
     */
    final int my_width = 0;
    /**
     *
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
     * @author allison
     *
     */
    final Rectangle my_a = new Rectangle();
    // my_a.my_rx = 10;
    //my_a.my_ry = 10;

    my_starshape = (Shape)my_a;

    return my_starshape;
  }

  public void shape(final Shape the_shape) {

    my_starshape = the_shape;

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

  public void animate() {
    // TODO Auto-generated method stub

  }

  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }

  public void animation(final Animation the_animation) {
    // TODO Auto-generated method stub

  }
  public Color color() {
    my_starcolor.equals(Color.WHITE);

    return my_starcolor;

  }

  public void color(final Color the_color) {

    my_starcolor = the_color;

  }

  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
