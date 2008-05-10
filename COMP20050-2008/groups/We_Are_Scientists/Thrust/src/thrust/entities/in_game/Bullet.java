/*
 * A re-implementation of the classic C=64 game 'Thrust'. @author "Joe Kiniry
 * (kiniry@acm.org)" @module "COMP 20050, COMP 30050" @creation_date "March
 * 2007" @last_updated_date "April 2008" @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

//import java.awt.Color;
import java.awt.Color;
import java.awt.Shape;

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
  /*
   * (non-Javadoc)
   *
   * @see thrust.physics.PhysicsInterface#mass()
   */

  /** the behaviour of the bullet. */
  private final transient EnemyEntityImp my_behaviour = new EnemyEntityImp();

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
  public Bullet(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_shapename,
      final Shape the_shape, final byte the_state) {
    super();
    super.set_dynamic_state(the_position, the_orientation, the_acceleration,
                        the_mass, the_velocity, the_shapename, the_shape,
                        the_state);

  }

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
    return java.awt.Color.BLACK;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.BLACK) {
      my_Color(java.awt.Color.BLACK);
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