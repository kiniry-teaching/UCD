package thrust.display;

import java.util.logging.Logger;

/**
 * Information about the game.
 *
 * @author Patrick Nevin (patrick.nevin@ucdconnect.ie)
 * @version 20 April 2008
 */
public class InfoPanel  extends AbstractInfoPanel {
  /**
   * whether the info panel is displayed.
   */
  boolean my_is_displayed;
  /**
   * @return Is the information panel currently displayed?
   */
  public /*@ pure @*/ boolean displayed() {
    return this.my_is_displayed;
  }
//We've yet decided how to display the high score, most likely we'll
  //add some widget to the JFrame and set its isVisable to true, so in
  //the mean time we'll just log
  /**
   * create a log of what to do.
   */
  Logger my_logger = Logger.getLogger("thrust.display.HighScoreDisplay");

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public void display() {
    my_logger.info("Most likely we'll display them in a JText area etc");
  }

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public void hide() {
    my_logger.info("Probably set the isVisable property to false");
  }

  /**
   * Update the displayed information panel.
   */
  public void update() {
    my_logger.info("do something!");
  }


}
