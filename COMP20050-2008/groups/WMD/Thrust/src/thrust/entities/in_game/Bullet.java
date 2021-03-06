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

import thrust.entities.DynamicEntity;
import thrust.entities.EnemyEntityInterface;
import thrust.entities.behaviors.AI;
import thrust.physics.Physic;

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 1 May 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntityInterface {

  /**
   * AI import.
   */
  AI my_ai = new AI();
/**
 * Physcs Import.
 */
  Physic my_physics = new Physic();

  /**
   * The mass of a bullet is 1kg.
   */
  final double my_bullet_mass;

  /**
   * The bullet's colour.
   */
  Color my_bullet_color;

  /**
   * Make a bullet.
   */
  public Bullet(final double[] a_position,
                final double an_orientation,
                final double[] an_acceleration,
                final double[] a_velocity,
                final String an_initial_shape_name,
                final Shape an_initial_shape,
                final byte an_initial_state,
                final Color a_color) {
    super();
    /**
     * The mass of a bullet is 1kg.
     */
    my_bullet_mass = 1;
    my_bullet_color = a_color;

    super.set_Dynamic_State(a_position, an_orientation,
                            an_acceleration, my_bullet_mass, a_velocity,
                            an_initial_shape_name, an_initial_shape,
                            an_initial_state);
  }


  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;


  /**
   * @return What is your attack behavior AI?
   */
  public AI attack() {
    return my_ai.attack(my_ai);
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  public void attack(final AI the_behavior) {
    my_ai.attack(the_behavior);
  }

  /**
   * @return What is your disturb behavior AI?
   */
  public AI disturb() {
    return my_ai.disturb(my_ai);
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behavior);
  }


  /**
   * @return What color are you?
   */
  public Color color() {
    return my_bullet_color;
  }

  /**
   * This is your color.
   * @the_color the new color.
   */
  public void color(final Color the_color) {
    my_bullet_color = the_color;

  }

  /**
   * @return What is your momentum?
   */
  public double momentum() {
    return my_physics.momentum();
  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
