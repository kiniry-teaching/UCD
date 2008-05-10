/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "simon markey (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */
package thrust.entities.in_game;

import java.awt.Color;
import java.awt.List;
import java.util.Collection;

import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
//import java.awt.Color;
//import java.awt.Shape;
//import thrust.animation.Animatable_class;
//import thrust.animation.Animation;
//import javax.swing.Timer;
//import java.awt.event.ActionEvent;
//import java.awt.event.ActionListener;
/**
 * The vacuum in which entities exist.
 * @author ursula redmond (ursula.redmond@ucdconnect.ie)
 * @version 10 May 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity
{

  /** Collection of stars. */
  private static final Collection STAR_COLLECTION = (Collection) new List();

  /**
   * @return What are your stars?"
   */
  public Collection stars() {
    return STAR_COLLECTION;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(final Star the_star) {
    STAR_COLLECTION.add(the_star);
  }

  public Color color() {
    return java.awt.Color.BLACK;
  }

  public void color(final Color the_color) {
    if (the_color == java.awt.Color.BLACK) {
      my_Color(java.awt.Color.BLACK);
    }
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
