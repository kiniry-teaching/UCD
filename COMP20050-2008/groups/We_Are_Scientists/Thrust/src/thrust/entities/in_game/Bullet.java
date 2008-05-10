/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;


import java.awt.Color;

// import thrust.animation.Animation;
import thrust.entities.DynamicEntity;
import thrust.entities.EnemyEntity;
import thrust.entities.EnemyEntityImp;
import thrust.entities.behaviors.AI;

/**
 * A bullet shot from the spaceship or a gun turret.
 *
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class Bullet extends DynamicEntity implements EnemyEntity {

  /** the behaviour of the bullet. */
  private final transient EnemyEntityImp my_behaviour = new EnemyEntityImp();

  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  // @ also ensures \result == 1;
  public double mass() {
    return 1;
  }


  public AI attack() {
    return my_behaviour.attack();
  }

  public void attack(final AI the_behavior) {
    my_behaviour.attack(the_behavior);

  }

  public AI disturb() {
    return my_behaviour.disturb();
  }

  public void disturb(final AI the_behavior) {
    my_behaviour.disturb(the_behavior);
  }

  public Color color() {
    return java.awt.Color.WHITE;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.WHITE) {
      my_Color(java.awt.Color.WHITE);
    }
  }

  /*
   * @ public invariant (* Bullets are destroyed on contact with a
   * @ barrier, a factory, a fuel pod, the goal
   * @ sphere, a gun turret, the spaceship, or the
   * @ terrain.
   */
  // @ public invariant (* Bullets have a mass of 1 kg. *);
}
