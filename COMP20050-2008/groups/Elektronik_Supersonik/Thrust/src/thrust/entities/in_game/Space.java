/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Shape;
import java.util.Collection;

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.animation.EntityAnimation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The vacuum in which entities exist.
 * 
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity implements NeutralEntity, Animatable {
  /**
   * The animation of space.
   */
  private EntityAnimation my_animation;
  
  /**
   * @param the_position
   * @param the_orientation
   * @param the_acceleration
   * @param the_mass
   * @param the_velocity
   * @param the_initial_shape_name
   * @param the_initial_shape
   * @param the_initial_state
   */
  
  public Space(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_initial_shape_name,
      final Shape the_initial_shape, final byte the_initial_state) {

    super();
    super.set_state(the_position, the_orientation, the_acceleration, the_mass,
                    the_velocity, the_initial_shape_name, the_initial_shape,
                    the_initial_state);

  }

  /**
   * @return What are your stars?"
   */
  public/* @ pure @ */Collection stars() {
    assert false; // @ assert false;
    return null;
  }

  /**
   * Add this star to space.
   * 
   * @param the_star
   *          the star to add.
   */
  public void add_star(Star the_star) {
    assert false; // @ assert false;
  }
  
  public void animate() {
    my_animation.animate();
  }

  public Animation animation() {
    return my_animation.animation();
  }

  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);
  }
  // @ public invariant (* Terrain and space are disjoint. *);
}
