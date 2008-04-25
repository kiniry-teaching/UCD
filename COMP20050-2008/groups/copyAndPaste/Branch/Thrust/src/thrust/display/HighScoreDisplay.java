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
   * create a log of what to do.
   */
  private Logger my_log = Logger.getLogger("thrust.display.HighScoreDisplay");
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
   * Display the high scores.
   */
  //@ ensures displayed();
  public void display() {
    my_log.info("Most likely we'll display them in a JText area etc");
  }

  /**
   * Hide the high scores.
   */
  //@ ensures !displayed();
  public void hide() {
    my_log.info("Probably set the isVisable property to false");
  }

  /**
   * Permit the player to add a new name for this high score.
   */
  public void add_new_high_score() {
    my_log.info("Add text to the text area?");
  }

}
