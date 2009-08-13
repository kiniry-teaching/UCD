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
import java.util.Random;

/**
 * A blinking star in space.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {
  /** Winking state of this star. */
  private transient boolean my_star_is_lit = true;

  /** Generate random numbers for winking. */
  private final transient Random my_random = new Random();

  public void animate() {
    // flip a coin three times; if we get three heads, flip our state
    if (my_random.nextBoolean() &
        my_random.nextBoolean() &
        my_random.nextBoolean()) {
      my_star_is_lit ^= my_star_is_lit;
    }
  }

  public Animation animation() {
    // skip
    return null;
  }

  public void animation(final Animation the_animation) {
    // ignore value of formal parameter and skip
  }

  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
