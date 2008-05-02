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
 * @author Simon markey,ursula redmond holly baker (kiniry@acm.org)
 * @version 11 April 2008
 */
public class HighScoreDisplay extends AbstractHighScoreDisplay {
  /**
   * @ booleans"
   */
  private boolean my_display;



  /**
   * @return Are the high scores currently displayed?"
   */
  public/*@ pure @*/ boolean displayed()
  {
    return my_display;
  }

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display()
  {
    if (!my_display)
    {
      my_display = true;
      System.out.print("on screen");

    }
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide()
  {
    if (my_display)
    {
      my_display = false;
      System.out.print("offscreen");
    }

  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void add_new_high_score()
  {
    final int[] score = new int[10];


  }
}
