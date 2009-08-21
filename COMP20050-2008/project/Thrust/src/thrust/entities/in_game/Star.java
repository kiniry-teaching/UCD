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

import thrust.animation.Animatable;
import thrust.animation.Animation;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {

  public void animate() {
    // TODO Auto-generated method stub
    
  }

  public Animation animation() {
    // TODO Auto-generated method stub
    return null;
  }

  public void animation(Animation the_animation) {
    // TODO Auto-generated method stub
    
  }
  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
