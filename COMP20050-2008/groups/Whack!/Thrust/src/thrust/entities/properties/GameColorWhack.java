package thrust.entities.properties;

import java.awt.Color;

/**
 * A color.
 * @author Allison Fallon (allison.fallon@ucdconnect.ie),
 * @       Tara Flood(Tara.Flood@ucdconnect.ie).
 * @version 21 April 2008
 */
public class GameColorWhack implements GameColor {
//@ public model Color _the_color;
  /**
   * implementing my color.
   */
  Color my_color;

  /**
   * @return What color are you?
   */
  //@ ensures \result == _the_color;
  public/*@ pure @*/ Color color() {

    my_color.equals(Color.BLUE);
    my_color.equals(Color.BLACK);
    my_color.equals(Color.RED);
    my_color.equals(Color.GRAY);
    my_color.equals(Color.ORANGE);
    my_color.equals(Color.MAGENTA);
    my_color.equals(Color.WHITE);
    my_color.equals(Color.GREEN);
    my_color.equals(Color.PINK);
    my_color.equals(Color.CYAN);
    my_color.equals(Color.DARK_GRAY);
    my_color.equals(Color.LIGHT_GRAY);


    return my_color;
  }

  /**
   * This is your color.
   * @the_color the new color.
   */
  //@ ensures color() == the_color;
  public void color(final Color the_color) {





    my_color = the_color;


  }

  //@ public invariant (* There are exactly 12 different colors available. *);
  /*@ public invariant _the_color == Color.BLACK | _the_color == Color.WHITE |
    @                  _the_color == Color.RED | _the_color == Color.GREEN |
    @                  _the_color == Color.BLUE | _the_color == Color.CYAN |
    @                  _the_color == Color.MAGENTA | _the_color == Color.DARK_GRAY |
    @                  _the_color == Color.GRAY | _the_color == Color.LIGHT_GRAY |
    @                  _the_color == Color.ORANGE | _the_color == Color.PINK;
    @*/
}
