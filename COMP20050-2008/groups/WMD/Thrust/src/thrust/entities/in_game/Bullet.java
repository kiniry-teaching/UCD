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
import thrust.entities.EnemyEntity;
import thrust.entities.behaviors.AI;

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 24 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {

  /**
   * The mass of a bullet is 1kg.
   */
  final double my_bullet_mass;
  /**
   * The shape of a bullet.
   */
  Shape my_bullet_shape;
  /**
   * The bullet's colour.
   */
  Color my_bullet_color;
  /**
   * The bullet's disturb.
   */
  AI my_disturb;
  /**
   * The bullet's attack.
   */
  AI my_attack;
  /**
   * The bullet's acceleration.
   */
  final double[] my_acceleration;
  /**
   * The bullet's momentum.
   */
  final double my_momentum;

  /**
   * Make a bullet.
   */
  public Bullet(final double[] a_acceleration,
                final double a_momentum) {

    /**
     * The mass of a bullet is 1kg.
     */
    my_bullet_mass = 1;

    my_acceleration = a_acceleration;
    my_momentum = a_momentum;

  }


  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;

  public double mass() {
    assert false; //@ assert false;
    return my_bullet_mass;
  }

  /**
   * Render yourself.
   */
  public void render() {
    // TODO Auto-generated method stub

  }

  /**
   * @return What shape are you?
   */
  public Shape shape() {
    return my_bullet_shape;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    my_bullet_shape = the_shape;
  }

  /**
   * @return What shape are you?
   */
  public String shape_name() {
    return "Rectangle";
  }

  /**
   * @return What is your physical state?
   * @note State is encoded by a non-negative number of "hit points".
   */
  public byte state() {
    // TODO Auto-generated method stub
    return 0;
  }

  /**
   * This is your physical state.
   * @param the_state the state.
   */
  public void state(final byte the_state) {
    // TODO Auto-generated method stub

  }

  /**
   * @return What is your attack behavior AI?
   */
  public AI attack() {
    return my_attack;
  }

  /**
   * @param the_behavior This is your attack behavior.
   */
  public void attack(final AI the_behavior) {
    my_attack = the_behavior;

  }

  /**
   * @return What is your disturb behavior AI?
   */
  public AI disturb() {
    return my_disturb;
  }

  /**
   * @param the_behavior This is your disturb behavior.
   */
  public void disturb(final AI the_behavior) {
    my_disturb = the_behavior;
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

  public double[] acceleration() {

    return my_acceleration;
  }

  public double gravitational_constant() {
    return null;
  }

  public double momentum() {
    return null;
  }

  public double orientation() {
    return null;
  }

  public double[] position() {
    return null;
  }

  public double[] velocity() {
    return null;
  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
