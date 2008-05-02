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
 * Top scores of past players.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 11 April 2008
 */
public class HighScoreDisplay {
  
  boolean displayed = false;
  char name;

  /**
   * @return Are the high scores currently displayed?"
   */
  public boolean displayed() {
    return displayed;
  }

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
    displayed = true;
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    displayed = false;
  }

  /**
   * Let the player to add a new name for this high score.
   */
  public void add_new_high_score() {
    //input a name by some method or other... for testing purposes, using:
    char n = 'DMG';
    name = n;
  }
}
