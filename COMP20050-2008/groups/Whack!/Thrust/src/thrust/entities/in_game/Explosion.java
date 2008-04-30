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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import thrust.animation.Animatable;
import thrust.animation.Animation;

/**
 * An explosion.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */

public class Explosion extends StaticEntity
  implements NeutralEntity, Animatable {
  /**
   * Static Entity.
   */
  StaticEntity my_staticentity;
  /**
   * acceleration.
   */
  double[] my_acceleration;
  /**
   * orientation.
   */
  double my_orientation;
  /**
   * position.
   */
  double[] my_position;
  /**
   * time.
   */
  double my_time;
  /**
   * velocity.
   */
  double[] my_velocity;
  /**
   * mass.
   */
  double my_mass;
  /**
   * my_animation.
   */
  Animation my_animation;
  /**
   * Color.
   */
  Color my_explosioncolor;

  public void animate() {
    // TODO Auto-generated method stub
  }

  public Animation animation() {
    return my_animation;
  }

  public void animation(final Animation the_animation) {
    my_animation = the_animation;

  }
  public double[] acceleration() {
    return my_acceleration;
  }

  public void acceleration(final double[] the_acceleration) {
    my_staticentity.acceleration();
  }

  public double gravitational_constant() {
    return my_staticentity.gravitational_constant();
  }
  public double mass() {
    my_mass = 1;
    return my_mass;
  }

  public void mass(final double the_mass) {
    my_staticentity.mass(the_mass);

  }

  public double orientation() {
    return my_orientation;
  }

  public void orientation(final double the_orientation) {
    my_staticentity.orientation(the_orientation);
  }

  public double[] position() {
    return my_position;
  }

  public void position(final double[] the_position) {
    my_staticentity.position(the_position);
  }

  public void simulate(final double some_seconds) {
    my_time = some_seconds;
  }

  public void velocity(final double[] the_velocity) {
    my_staticentity.velocity(the_velocity);
  }

  public Color color() {
    my_explosioncolor.equals(Color.GREEN);
    return my_explosioncolor;
  }

  public void color(final Color the_color) {
    my_explosioncolor = the_color;
  }

}
