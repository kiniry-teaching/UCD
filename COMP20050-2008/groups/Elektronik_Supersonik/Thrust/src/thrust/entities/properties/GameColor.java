/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.properties;

import java.awt.Color;

/**
 * A color.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public interface GameColor {
  // @ public model Color _the_color;

  /**
   * @return What color are you?
   */
  // @ ensures \result == _the_color;
  /* @ pure @ */Color color();

  /**
   * This is your color.
   * @the_color the new color.
   */
  // @ ensures color() == the_color;
  void color(Color the_color);

  // @ public invariant (* There are exactly 12 different colors available. *);
  /*
   * @ public invariant _the_color == Color.BLACK | _the_color == Color.WHITE |
   * @ _the_color == Color.RED | _the_color == Color.GREEN | @ _the_color ==
   * Color.BLUE | _the_color == Color.CYAN | @ _the_color == Color.MAGENTA |
   * _the_color == Color.DARK_GRAY | @ _the_color == Color.GRAY | _the_color ==
   * Color.LIGHT_GRAY | @ _the_color == Color.ORANGE | _the_color == Color.PINK;
   */
}
