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
import thrust.entities.NeutralEntity;
import thrust.entities.behaviors.Tow;

/**
 * The goal sphere that the spaceship needs to tow into
 * space away from the terrain to escape.
 * @author jdouglas (jd2088@gmail.com)
 * @version 18 April 2008
 */
public class GoalSphere extends DynamicEntity
  implements NeutralEntity, Tow {

  public GoalSphere(final double[] the_position,
                    final double the_orientation, final Color the_color,
                    final String the_initial_shape_name,
                    final Shape the_initial_shape,
                    final byte the_initial_state,
                    final double[] the_acceleration,
                    final double[] the_velocity,
                    final double the_mass,
                    final double some_seconds) {

    super();
    super.set_the_state(the_position, the_orientation, the_color,
                    the_initial_shape_name, the_initial_shape,
                    the_initial_state, the_acceleration, the_velocity,
                    the_mass, some_seconds);
  }

  /*@ public invariant (* The fuel pod is destroyed by a bullet. *);
    @ public invariant (* If the fuel pod is destroyed, the spaceship
    @                     is destroyed. *);
    @ public invariant (* The goal sphere is destroyed by the factory's
    @                     chimney, but not its sphere. *);
    @ public invariant (* The goal sphere is not affected by the gun turret. *);
    @ public invariant (* The goal sphere is not affected by the fuel pod. *);
    @ public invariant (* The goal sphere is not affected by space. *);
    @ public invariant (* The goal sphere is not affected by stars. *);
    @ public invariant (* The goal sphere is destroyed by the terrain. *);
    @ public invariant (* When rendered on the terrain, the goal sphere
    @                     sits on a pedestal. *);
    @ public invariant (* When being towed, the goal sphere is rendered
    @                     as a sphere. *);
    @ public invariant (* The shape of the goal sphere is always a circle. *);
    @ public invariant (* The colour of the goal sphere is always green. *);
    @ public invariant colour() == thrust.entities.properties.GameColor.GREEN;
    @*/
}
