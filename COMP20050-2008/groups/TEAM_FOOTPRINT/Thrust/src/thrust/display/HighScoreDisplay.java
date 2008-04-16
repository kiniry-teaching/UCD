package thrust.display;

/**
 * Top scores of past players.
 *
 * @author Daire O'Doherty 06535691 15/4/08
 * @version 15 April 2008
 */
public class HighScoreDisplay extends AbstractHighScoreDisplay {
  /**
   * @return Are the high scores currently displayed?"
   */

  public boolean isDisplayed;
  public boolean displayed() {
    return isDisplayed = true;
  }

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void addNewHighScore() {
  }
}

