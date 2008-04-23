/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities;

import thrust.physics.Physics;

/**
 * Entities whose position or orientation change.
 * @author Joe Kiniry (kiniry@acm.org)
 * @edited Tara Flood (Tara.Flood@ucdconnect.ie)
 * @version 21 April 2008
 */
public abstract class DynamicEntity extends Entity
  implements Physics {
}
