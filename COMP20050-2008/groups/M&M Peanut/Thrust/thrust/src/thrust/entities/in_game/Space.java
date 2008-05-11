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

import java.util.Collection;

import thrust.animation.Animatable;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * @author Sean Jago
 * @version 1 May
 */

public class Space extends StaticEntity implements NeutralEntity, Animatable
{

 /**
  * stars
  */

  private Star[] my_stars;

 /**
  * static entity
  */ 

  private StaticEntity my_static;

 /**
  * animatable entity
  */
 
  private Animatable my_anim;

  public Space(final Star[] the_stars)
  {
   my_stars = the_stars;
  }

  /**
   * @return What are your stars?"
   */
   public /*@ pure @*/ Collection stars() 
   {
    assert false; //@ assert false;
    return null;
   }

 /**
   * Add this star to space.
   * @param the_star the star to add.
   */

   public void add_star(final Star the_star)
   {
    final int length = my_stars.length;
    my_stars = the_star;
   }

   public double acceleration (final double[] the_acceleration)
   {
    my_static.acceleration(the_acceleration);
   }

   public double mass()
   {
    return 0;
   }

   public double[] velocity()
   {
    return my_static.velocity();
   }
   
   public double momentum()
   {
    return my_static.momentum();
   }

   public Shape shape()
   {
    return my_static.shape();
   }
  
   public void animate()
   {
    my_anim.animate();
   }

   public Animation animation()
   {
    my_anim.animation();
   }

   public Color color()
   {
    return my_static.color();
   }

   public double orientation() 
   {
    return my_static.orientation;
   }

   public double my_gravity()
   {
    return 0;
   }
  
   public void acceleration(final double[] the_acceleration)
   {  
    my_static.acceleration(the_acceleration);
   }
 
   public void mass(final double the_mass)
   {
    my_static.mass(the_mass);
   }

   public void shape(final Shape the_shape)
   {
    my_static.shape(the_shape)
   }

   public void animation(final Animation the_animation)
   {
    my_anim.animation(the_animation);
   }

   public void color(final Color the_color)
   {
    my_static.color(the_color);
   }
   
   public void velocity(final double[] the_velocity)
   {
    my_static.velocity(the_velocity);
   }

   public void orientation(final double the_orientation)
   {
    my_static.orientation(the_orientation);
   }
 
   public void position(final double[] the_position)
   {  
    my_static.position(the_position);
   }
   
}
   