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
  //@ also ensures \result == 1;
  /**
   * The AI of an attacking bullet.
   */
  private AI my_attackAI;
  /**
   * The ai of a disturbing bullet.
   */
  private AI my_disturbAI;
  /**
   * The color of the bullet.
   */
  private Color my_color;
  public void attack(final AI the_behaviour) {
    my_attackAI = the_behaviour;
  }
  public void disturb(final AI the_behaviour) {
    my_disturbAI = the_behaviour;
  }
  public AI attack() {
    return my_attackAI;
  }
  public AI disturb() {
    return my_disturbAI;
  }
  public double mass() {
    return 1;
  }
  public void color(final Color the_color) {
  }
  public Color color() {
    return my_color;
  }
  public void simulate(final double the_amount) {
  }
 /* public void color(final Color the_color) {
    my_color = the_color;
  }
  public GameColor. color() {
    return my_color.color();
  }*/
  /*@ public invariant (* Bullets are destroyed on contact with a
    @                     barrier, a factory, a fuel pod, the goal
    @                     sphere, a gun turret, the spaceship, or the
    @                     terrain. *);
    @*/
  //@ public invariant (* Bullets have a mass of 1 kg. *);
}
