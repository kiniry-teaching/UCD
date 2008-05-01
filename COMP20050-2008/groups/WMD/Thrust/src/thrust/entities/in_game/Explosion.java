
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
//import thrust.entities.behaviors.AI;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 1 May 2008
 */
public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {

  /**
   * The shape of an explosion.
   */
  Shape my_explosion_shape;

  /**
   * The state of the explosion.
   */
  byte my_state;

  /**
   * The explosion's animation.
   */
  Animation my_animation;

  /**
   * The explosion's color.
   */
  Color my_color;

  /**
   * @param acceleration
   * @param mass
   * @param momentum
   * @param velocity
   */
  public Explosion(final double[] an_acceleration,
                   final double[] a_position,
                   final double an_orientation,
                   final double a_mass,
                   final double[] a_velocity,
                   final String an_initial_shape_name,
                   final Shape an_initial_shape,
                   final byte an_initial_state) {
    super();
    super.set_Staticstate(a_position, an_orientation,
                          an_acceleration, a_mass, a_velocity,
                          an_initial_shape_name, an_initial_shape,
                          an_initial_state);


  }

  public void animate() {

  }

  public Animation animation() {

    return null;
  }

  public void animation(final Animation the_animation) {

  }

  public Color color() {
    return null;
  }

  public void color(final Color the_color) {

  }

}
