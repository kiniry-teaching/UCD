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

/**
 * Information about the game.
 *
 * @author David McGinn
 * @author Michael Fahey
 * @author Cillian O'Neill
 * @version 2 May 2008
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
     System.out.println("High score is displayed");
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
   /**     NOT FINISHED
    *   cur_score = score();
    *   cur_lives = lives();
    *   cur_fuel = current_fuel();
    */
  }
}
