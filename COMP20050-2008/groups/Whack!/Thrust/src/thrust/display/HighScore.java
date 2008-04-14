package thrust.display;
/**
 * @author Tara Flood (0361188@ucdconnect.ie)
 * @version 14 April 2008
 */
public class HighScore extends AbstractHighScoreDisplay {
  /**
   * @return Are the high scores currently displayed?"
   */
  public boolean displayed() {
    return true;
  }

  /**
   * Display the high scores.
   */
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
  public void add_new_high_score() {

  }
}
