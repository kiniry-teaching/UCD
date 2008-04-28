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

import java.util.Collection;

import thrust.animation.Animatable;
import thrust.entities.NeutralEntity;
import thrust.entities.StaticEntity;
import java.awt.Color;
import java.awt.Shape;
import thrust.animation.Animation_class;
import thrust.animation.Animation;
import javax.swing.Timer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
/**
 * The vacuum in which entities exist.
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 18 April 2008
 */
public class Space extends StaticEntity
  implements NeutralEntity
  {
  /**
   * @return What are your stars?"
   */
  public /*@ pure @*/ Collection stars() {
    assert false; //@ assert false;
    return null;
  }

  /**
   * Add this star to space.
   * @param the_star the star to add.
   */
  public void add_star(Star the_star) {
  //  assert false; //@ assert false;
    
    Star add_star = the_star;
  }

  //@ public invariant (* Terrain and space are disjoint. *);
}
