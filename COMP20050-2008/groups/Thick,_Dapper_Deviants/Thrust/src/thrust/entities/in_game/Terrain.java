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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The planet on which some entities rest.
 * @author David Murphy(05590701)
 * @version  4 May 2008.
 */
public class Terrain extends StaticEntity
  implements NeutralEntity {
  /*@ public invariant (* Terrain and space are disjoint. *);
    @ public invariant (* The shape of the terrain is rendered as a
    @                     sequence of horizontal lines. *);
    @*/
  private static double[] my_position;
  private static double my_orientation;
  public void set_terrain_state(final double[] the_position ,
                                final double the_orientation) {
    super.set_state(my_position = new double[] {the_position[0] , the_position[1]}, 
                    my_orientation = the_orientation);
    }
}
