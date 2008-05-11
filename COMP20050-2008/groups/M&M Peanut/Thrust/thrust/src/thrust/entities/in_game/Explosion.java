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
import thrust.animation.Animatable;

/**
 * An explosion.
 * @author Sean Jago
 * @version 1 May
 */


public class Explosion extends StaticEntity implements NeutralEntity, Animatable
{
 /**
  * static entity
  */
  
  private StaticEntity my_static;

 /**
  * acceleration
  */
  
  private double[] my_acceleration;

 /**
  * orientation
  */
 
  private double[] orientation;
 
 /**
  * position
  */

  private double[] my_position;
 
 /**
  * velocity
  */
  
  private double[] my_velocity;

 /**
  * mass
  */

  private double my_mass;
 
 /**
  * animation
  */
  
  private Animation my_anim;

 /**
  * color
  */

  private Color my_excolor;
 
 
  public Animation animation()
  {
   return my_anim;
  }

  public double[] acceleration()
  {
   return acceleration;
  }

  public double my_gravity()
  {
   return my_static.my_gravity();
  }

  public double mass()
  {
   return my_static.mass;
  }

  public double orientation()
  {
   return my_static.orientation;
  }

  public double[] position()
  {
   return my_static.position;
  }

  public Color color()
  {
   my_excolor.equals(Color.RED);
   return my_excolor;
  }

  public void color(final Color the_color)
  {
   my_excolor = the_color;
  }

  public void animation(final Animation the_animation)
  {
   my_anim = the_animation;
  }

  public void acceleration(final double[] the_acceleration)
  {
   my_static.acceleration(the_acceleration);
  }

  public void mass (final double the_mass)
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

  public void velocity(final double[] the_velocity)
  {
   my_static.velocity(the_velocity);
  }

}

  

  