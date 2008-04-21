package thrust.display;
import java.util.logging.Logger;
/**
 * Top scores of past players.
 *
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 20 April 2008
 */
public class HighScoreDisplay extends AbstractHighScoreDisplay {
  /**
   * are high scores displayed.
   */
  private boolean my_displayed;
  /**
   * @return Are the high scores currently displayed?"
   */
  public /*@ pure @*/ boolean displayed() {
    return this.my_displayed;
  }
//We've yet decided how to display the high score, most likely we'll
  //add some widget to the JFrame and set its isVisable to true, so in
  //the mean time we'll just log
  /**
   * create a log of what to do.
   */
  final Logger my_logger = Logger.getLogger("thrust.display.HighScoreDisplay");
  /**
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
    my_logger.info("Most likely we'll display them in a JText area etc");
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    my_logger.info("Probably set the isVisable property to false");
  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void add_new_high_score() {
    my_logger.info("Add text to the text area?");
  }

}
