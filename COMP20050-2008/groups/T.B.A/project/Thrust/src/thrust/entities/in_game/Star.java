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
import thrust.animation.Animatable;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * A blinking star in space.
 * @author jdouglas (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Star extends StaticEntity
  implements NeutralEntity, Animatable {
/**.
   * This is for the animation of a star
   */
  private Animatable my_animation;

  public Star(final double[] the_position,
            final double the_orientation, final Color the_color,
            final String the_initial_shape_name,
            final Shape the_initial_shape,
            final byte the_initial_state) {

  super();
    super.set_state(the_position, the_orientation, the_color,
                  the_initial_shape_name,
                  the_initial_shape,
                  the_initial_state);

  }

  /*public void animate() {
    my_animation.animate();
  }

  public Animation animation() {
    return my_animation.animation();
  }*/

  /*@ public invariant (* A star's location is in space. *);
    @ public invariant (* A star interacts with no other entities. *);
    @ public invariant (* Each star blinks irregularly. *);
    @ public invariant (* A star's shape is always a small square. *);
    @*/
}
