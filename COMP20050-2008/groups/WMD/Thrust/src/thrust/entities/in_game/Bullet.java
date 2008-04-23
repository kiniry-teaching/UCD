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
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;
  public double mass() {
    assert false; //@ assert false;
    return 0;
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
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * This is your shape.
   * @param the_shape the shape of this Entity.
   */
  public void shape(final Shape the_shape) {
    // TODO Auto-generated method stub

  }

  /**
   * @return What shape are you?
   */
  public String shape_name() {
    // TODO Auto-generated method stub
    return null;
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

  public AI attack() {
    // TODO Auto-generated method stub
    return null;
  }

  public void attack(final AI the_behavior) {
    // TODO Auto-generated method stub

  }

  public AI disturb() {
    // TODO Auto-generated method stub
    return null;
  }

  public void disturb(final AI the_behavior) {
    // TODO Auto-generated method stub

  }


  /**
   * @return What color are you?
   */
  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * This is your color.
   * @the_color the new color.
   */
  public void color(Color the_color) {
    // TODO Auto-generated method stub

  }

  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
