/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.display;
package thrust.entities.about;
import thrust.entities.about.*;

/**
 * Information about the game.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 11 April 2008
 */
public class InfoPanel {
  int cur_score;
  byte cur_lives;
  int cur_fuel;
  boolean displayed = false;
  /**
   * @return Is the information panel currently displayed?
   */
  public boolean displayed() {
    return displayed;     
  }

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public void display() {
     displayed = true;
  }

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public void hide() {
    displayed = false;
  }

  /**
   * Update the displayed information panel.
   */
  public void update() {
    cur_score = GameState.score();
    cur_lives = GameState.lives();
    cur_fuel = GameState.current_fuel();
  }
}
