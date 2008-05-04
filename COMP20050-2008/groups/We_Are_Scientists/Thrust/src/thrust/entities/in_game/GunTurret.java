/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;
import thrust.entities.in_game.Star.Point;
import thrust.entities.in_game.Star.Rectangle;

import java.awt.Color;
import java.awt.Shape;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * 
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GunTurret extends StaticEntity implements EnemyEntity {
  /**
   * The gun's colour.
   */
  private transient Color my_gunColor;
  /**
   * The Speed.
   */
  public static final double SPEED = 0;
  /**
   * The angle in radians.
   */
  //private final double my_anglerad = Double.POSITIVE_INFINITY;

  /**
   * @return The turret's attack AI must shoot a bullet toward the spaceship.
   */
  public AI attack() {
    assert false; // @ assert false;
    return null;
  }

  /**
   * @param the_behavior
   *          The turret's attack AI must shoot a bullet toward the spaceship.
   */
  public void attack(final AI the_behavior) {
    assert false; // @ assert false;
  }

  /**
   * @return The turret's disturb AI must shoot a bullet in a random direction
   *         away from the terrain.
   */
  public AI disturb() {
    assert false; // @ assert false;
    return null;
  }

  /**
   * @param the_behavior
   *          The turret's disturb AI must shoot a bullet in a random direction
   *          away from the terrain.
   */
  public void disturb(final AI the_behavior) {
    assert false; // @ assert false;
  }

  /*
   * @ public invariant (* A gun turret always resides on/adjacent to @ the
   * terrain. *); @ public invariant (* A gun turret's color is always green.
   * *); @ public invariant color() == java.awt.Color.GREEN; @
   */

  public Color color() {

    my_gunColor = Color.GREEN;

    return my_gunColor;

  }

  public void color(final Color the_color) {

    my_gunColor = the_color;

  }

  public String shape_name() {
    return "Gun";
  }

  /**
   * The rectangle class.
   * @author ursula
   *
   */
  public class Rectangle {
    /**
     * width of rectangle.
     */
    //private final transient int my_width = 1;
    /**
     * height of rectangle.
     */
   //private final transient int my_height = 1;
    /**
     *
     */
    //private final transient Point my_origin;

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
    final Rectangle my_a = new Rectangle(10, 10);

    final Shape my_Gunshape = (Shape) my_a;

    return my_Gunshape;

  }

/**
 * The Point class.
 * @author ursula
 *
 */
  public class Point {
    /**
     * The x coordinate.
     */
    private final transient int my_x = (int) Math.random();
    /**
     * The y coordinate.
     */
    private final transient int my_y = (int) Math.random();

    public int the_x() {
      return my_x;
    }

    public int the_y() {
      return my_y;
    }

   /* public Point(final int the_x, final int the_y) {
      my_x = the_x;
      my_y = the_y;
    }*/
  }

}
