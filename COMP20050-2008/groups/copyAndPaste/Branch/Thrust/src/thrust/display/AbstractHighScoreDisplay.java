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
public abstract class AbstractHighScoreDisplay {
  /**
   * @return Are the high scores currently displayed?"
   */
  public abstract /*@ pure @*/ boolean displayed();

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public abstract void display();

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public abstract void hide();

  /**
   * Permit the player to add a new name for this high score.
   */
  public abstract void add_new_high_score();
}
