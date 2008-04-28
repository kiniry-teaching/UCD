package thrust.entities.properties;

import java.awt.Color;

/**
 * A color.
 * @author Patrick Nevin (Patrick.Nevin@ucdconnect.ie)
 * @version 25 April 2008
 */
public class GameColorClass implements GameColor {
  /**the entities color.*/
  private Color my_color;

  /**set the entities color.*/
  public GameColorClass(final Color a_color) {
    this.my_color = a_color;
  }
  /**
   * @return What color are you?
   */
  //@ ensures \result == _the_color;
  public Color color() {
    return my_color;
  }
  /**
   * This is your color.
   * @the_color the new color.
   */
  //@ ensures color() == the_color;
  public void color(final Color the_color) {
    this.my_color = the_color;
  }

}
