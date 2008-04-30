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

import java.awt.Shape;

import thrust.entities.EnemyAI;
import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;
import thrust.entities.behaviors.AI;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GunTurret extends StaticEntity implements EnemyEntity {
  /**
   * The AI of the gun turret.
   */
  private transient EnemyAI my_ai;
  public GunTurret(final double[] the_position, final double the_orientation,
      final double[] the_acceleration, final double the_mass,
      final double[] the_velocity, final String the_initial_shape_name,
      final Shape the_initial_shape, final byte the_initial_state) {

    super();
    super.set_state(the_position, the_orientation, the_acceleration, the_mass,
                    the_velocity, the_initial_shape_name, the_initial_shape,
                    the_initial_state);

  }

  /**
   * @return The turret's attack AI must shoot a bullet toward the spaceship.
   */
  public AI attack() {
    return my_ai.attack();
  }

  /**
   * @param the_behavior The turret's attack AI must shoot a bullet toward
   * the spaceship.
   */
  public void attack(final AI the_behavior) {
    my_ai.attack(the_behavior);
  }

  /**
   * @return The turret's disturb AI must shoot a bullet in a random direction
   * away from the terrain.
   */
  public AI disturb() {
    return my_ai.disturb();
  }

  /**
   * @param the_behavior The turret's disturb AI must shoot a bullet
   * in a random direction away from the terrain.
   */
  public void disturb(final AI the_behavior) {
    my_ai.disturb(the_behavior);
  }

  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == java.awt.Color.GREEN;
    @*/
}
