/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Keith Madden (keith.madden@ucdconnect.ie)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

/**
 * An entity that is not a threat and is not helpful to the spaceship.
 * @author Keith Madden (keith.madden@ucdconnect.ie)
 * @version 30 April 2008
 */
public interface NeutralEntity {
  /**
   * factory.
   */
  NeutralEntity my_factory;
  /**
   * Pedestal.
   */
  NeutralEntity my_pedestal;
  /**
   * Star.
   */
  NeutralEntity my_star;
  /**
   * Barrier.
   */
  NeutralEntity my_barrier;
  /**
   * Bullet.
   */
  NeutralEntity my_bullet;
  /**
   * Explosion.
   */
  NeutralEntity my_explosion;
  /**
   * Space.
   */
  NeutralEntity my_space;
  /**
   * Terrain.
   */
  NeutralEntity my_terrain;
}
