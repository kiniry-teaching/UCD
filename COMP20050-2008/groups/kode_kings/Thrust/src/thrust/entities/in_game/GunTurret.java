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

import thrust.entities.EnemyEntity;
import thrust.entities.StaticEntity;

/**
 * An enemy gun turret that shoots bullets at the spaceship.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class GunTurret extends StaticEntity
  implements EnemyEntity {
  /*@ public invariant (* A gun turret always resides on/adjacent to
    @                     the terrain. *);
    @ public invariant (* A gun turret's color is always green. *);
    @ public invariant color() == thrust.entities.properties.GameColor.GREEN;
    @*/
}
