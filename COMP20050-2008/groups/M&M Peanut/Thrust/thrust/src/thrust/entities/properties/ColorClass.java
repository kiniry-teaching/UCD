package thrust.entities.properties

import java awt.Color;

/**
 * A Color.
 * @author Sean Jago
 * @version 19 April 2008	
 */

Public class ColorClass implements GameColor
{
 private Color my_color;

 /**
  * entity color.
  */

 public ColorClass(final Color _the_color)
 {
  my_color = _the_color;
 }

 /**
   * @return What color are you?
   */
  //@ ensures \result == _the_color;
  /*@ pure @*/ Color color();

 public Color color()
 {
  return my_color;
 }
  
 
  /**
   * This is your color.
   * @the_color the new color.
   */ 
 public void color(final Color the_color)
 {
  my_color = the_color;
 }

}