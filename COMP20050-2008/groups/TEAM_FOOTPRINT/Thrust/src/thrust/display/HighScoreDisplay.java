package thrust.display;

import java.util.logging.Logger;

/**
 * Top scores of past players.
 *
 * @author "Daire O'Doherty 06535691 (daireod@gmail.com)"
 * @version 15 April 2008
 */
public class HighScoreDisplay extends AbstractHighScoreDisplay {
  /**
   * logger for output.
   */
  private final Logger my_log = Logger.getLogger("thrust.input.InputHandler");
  /**
   * @return Are the high scores currently displayed?"
   */

  private boolean my_is_displayed;
  public boolean displayed() {
    return my_is_displayed;
  }

  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
    if (!displayed()) {
      my_is_displayed = true;
      my_log.info("Display");
    }
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    if (displayed()) {
      my_is_displayed = false;
      my_log.info("Display");
    }
  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void addNewHighScore() {
  }
}

