package thrust.display;

/**
 * Top scores of past players.
 *
 * @author Siobhan Dunne (Siobhan.Dunne@ucd.ie)
 * @version 14 April 2008
 */

public class HighScoreDisplay extends AbstractHighScoreDisplay {

  /**
   * @return Are the high scores currently displayed?"
   */
  private boolean my_display;

  /**
   * @return Are the high scores currently displayed?"
   */
  public /*@ pure @*/ boolean displayed() {
    return my_display;
  }

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
    if (!displayed()) {
      System.out.print("display");
      my_display = true;
      //display
    }
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    if (displayed()) {
      System.out.print("hide");
      my_display = false;
    }
  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void add_new_high_score() {

  }
}
