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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The planet on which some entities rest.
 * @author Sean Jago
 * @version 1 May 2008
 */


public class Terrain extends StaticEntity implements NeutralEntity
{

/**
 * static entity
 */
 
   StaticEntity my_static;

/**
 * mass
 */

   double my_mass;

/**
 * orientation
 */

   double my_orientation;

/**
 * position
 */

   double[] my_position;

/**
 * color
 */
  
   Color my_landcolor;

/**
 * time
 */

   double my_time;


   public void acceleration (final double[] the_acceleration)
   {
    my_static.acceleration(the_acceleration);
   }

   public double my_gravity()
   {
    return my_static.my_gravity();
   }

   public double mass()
   {
    return my_mass;
   }

   public double orientation()
   {
    return mt_orientation;
   }

   public double[] position()
   {
    return my_position;
   }

   public Color color() 
   {
    my_landcolor.equals(Color.GREEN);
    return my_landcolor;
   }

   public void color(final Color the_color)
   {
    my_landcolor = the_color;
   }

   public void mass(final double the_mass)
   {
    my_static.mass(the_mass);
   }

   public void orientation(final double the_orientation)
   {
    my_static.orientation(the_orientation);
   }
  
   public void position(final double[] the_position)
   {  
    my_static.position(the_position);
   }

  
 