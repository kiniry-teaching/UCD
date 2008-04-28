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
/*import thrust.entities.behaviors.AI;
import thrust.entities.EnemyAI;*/

/**
 * A bullet shot from the spaceship or a gun turret.
 * @author David Haughton (dave.haughton1@gmail.com)
 * @version 18 April 2008
 */
public class Bullet extends DynamicEntity
  implements EnemyEntity {
  /* (non-Javadoc)
   * @see thrust.physics.PhysicsInterface#mass()
   */
  //@ ensures \result == 1;
/**
 * The color of the bullet.
 */
  Color my_color = Color.RED;
  public Bullet(
                final double[] the_position,
                final double the_orientation,
                final String the_initial_shape_name,
                final Shape the_initial_shape,
                final byte the_initial_state,
                final double[] the_acceleration,
                final double[] the_velocity,
                final double some_seconds,
                final double the_momentum
  )
  {
    super.set_the_state(
                        the_position,
                        the_orientation, my_color,
                        the_initial_shape_name,
                        the_initial_shape,
                        the_initial_state,
                        the_acceleration,
                        the_velocity,
                        mass(),
                        some_seconds,
                        the_momentum);

  }
  /*@ public invariant (* Bullets are destroyed othe_momentumn contact with a
  @                     barrier, a factory, a fuel pod, the goal
  @                     sphere, a gun turret, the spaceship, or the
  @                     terrain. *);
  @*/
//@ public invariant (* Bullets have a mass of 1 kg. *);

  public double mass() {
    return 1;
  }

}
