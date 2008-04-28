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

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;

/**
 * The planet on which some entities rest.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Terrain extends StaticEntity
  implements NeutralEntity {

  public double gravitational_constant() {
    // TODO Auto-generated method stub
    return 0;
  }

  public void simulate(final double some_seconds) {
    // TODO Auto-generated method stub
  }

  public Color color() {
    // TODO Auto-generated method stub
    return null;
  }

  public void color(final Color the_color) {
    // TODO Auto-generated method stub
  }
  /*@ public invariant (* Terrain and space are disjoint. *);
    @ public invariant (* The shape of the terrain is rendered as a
    @                     sequence of horizontal lines. *);
    @*/
}
