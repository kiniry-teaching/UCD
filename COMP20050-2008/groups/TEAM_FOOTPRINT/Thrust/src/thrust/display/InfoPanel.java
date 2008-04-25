package thrust.display;
import java.util.logging.Logger;

/**
 * @author Daire O'Doherty 06535691 (daireod@gmail.com)
 * @version 18 April 2008
 */
public class InfoPanel extends AbstractInfoPanel {
  /**
   * logger for output.
   */
  private final Logger my_log = Logger.getLogger("thrust.input.InputHandler");
  /**
   * @return Is the information panel currently displayed?
   */
  private boolean my_is_displayed;

  public /*@ pure @*/ boolean displayed() {
    return my_is_displayed;
  }

  /**
   * Display the information panel.
   */
  //@ ensures displayed();
  public void display() {
    if (!displayed()) {
      my_is_displayed = true;
      my_log.info("Display");
    }
  }

  /**
   * Hide the information panel.
   */
  //@ ensures !displayed();
  public void hide() {
    if (!displayed()) {
      my_is_displayed = false;
      my_log.info("Display");
    }
  }

  /**
   * Update the displayed information panel.
   */
  public void update() {

  }
}

