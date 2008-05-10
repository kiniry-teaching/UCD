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

import java.awt.Color;
import java.awt.Shape;

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.AnimatableImp;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author simon, ursula (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  /** The explosion's animation. */
  private transient AnimatableImp my_animation;

  /**
  *
  * @param the_position
  * @param the_orientation
  * @param the_acceleration
  * @param the_mass
  * @param the_velocity
  * @param the_shapename
  * @param the_shape
  * @param the_state
  */
  public Explosion(final double[] the_position, final double the_orientation,
     final double[] the_acceleration, final double the_mass,
     final double[] the_velocity, final String the_shapename,
     final Shape the_shape, final byte the_state) {
    super();
    super.set_dynamic_state(the_position, the_orientation, the_acceleration,
                       the_mass, the_velocity, the_shapename, the_shape,
                       the_state);
  }

  /*
   * Explode.
   */
  public void explode() {
    animate();
  }

  /*
   * (non-Javadoc)
   * @see thrust.animation.Animatable#animate()
   */
  public void animate() {
    my_animation.animate();
  }

  /*
   * (non-Javadoc)
   * @see thrust.animation.Animatable#animation()
   */
  public Animation animation() {
    return my_animation.animation();
  }

  /*
   * (non-Javadoc)
   * @see thrust.animation.Animatable#animation(thrust.animation.Animation)
   */
  public void animation(final Animation the_animation) {
    my_animation.animation(the_animation);
  }

  /*
   * An explosion is white.
   * (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color()
   */
  public Color color() {
    return java.awt.Color.WHITE;
  }

  /*
   * (non-Javadoc)
   * @see thrust.entities.properties.GameColor#color(java.awt.Color)
   */
  public void color(final Color the_color) {
    if (the_color == java.awt.Color.WHITE) {
      my_Color(java.awt.Color.WHITE);
    }
  }

}
