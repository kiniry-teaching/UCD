/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package.thrust.entities;

import thrust.entities.properties.GameColor;
import java.awt.Shape;
import java.awt.Color;

/**
 * Any entity in the game that is drawn in space or on the terrain.
 * @author Sean Jago
 * @version 26 April 2008
 */

public class Entity implements GameColor
{

/**
 * Set the initial shape name, shape, and state of this entity.
 * @param the_initial_shape_name the initial shape name.
 * @param the_initial_shape the initial shape.
 * @param the_initial_state the initial state.
 */

   private String my_initial_shape_name;
   private Shape my_initial_shape;
   private byte my_initial_state;
   private Color my_color;
 
/**
 * create the entity
 */
   public Entity()
   {
   
   }

/**
 * Set the initial shape name, shape, and state of this entity.
 * @param the_initial_shape_name the initial shape name.  
 * @param the_initial_shape the initial shape. 
 * @param the_initial_state the initial state.
 * @param the_color the color of the entity.
 */

  public void set_state(final String the_initial_shape_name,
                        final Shape the_initial_shape,
                        final byte the_initial_state,
                        final Color the_color) 
  {
    this.my_initial_shape_name = the_initial_shape_name;
    this.my_initial_shape = the_initial_shape;
    this.my_initial_state = the_initial_state;
    my_color = the_color;
  }

/**
 * @return What shape are you?
 */
  
   public String shape_name()
   {
    return my_initial_shape_name;
   }

/**
 * @return What shape are you?
 */

   public Shape shape() 
   {
    return my_initial_shape;
   }

/**
 * This is your shape.
 * @param the_shape the shape of this Entity.
 */

   public void shape(final Shape the_shape) 
   {
    this.my_initial_shape = the_shape;
   }
 
/**
 * @return What is your physical state?
 * @note State is encoded by a non-negative number of "hit points".
 */

   public byte state() 
   {
    return my_initial_state;
   }

/**
 * This is your physical state.
 * @param the_state the state.
 */

   public void state(final byte the_state)
   {
    this.my_initial_state = the_state;
   }

/**
 * Render yourself.
 */

  public void render() 
  {
    assert false; 
  }

/**
 * Return your color.
 * @return What color are you?
 */

  public Color color()
  {
   return my_color;
  }

/**
 * Set your color.
 * @param the_color the color to set the entity to.
 */

  public void color(final Color the_color)
  {
   my_color = the_color;
  }

}