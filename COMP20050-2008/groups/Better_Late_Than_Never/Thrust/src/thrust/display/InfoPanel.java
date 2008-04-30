package thrust.display;

/**
 * Information about the game.
 *
 * @author Joe Kiniry (kiniry@acm.org) <- essentially
 * @version 11 April 2008
 */

public class InfoPanel extends AbstractInfoPanel {

  /** Boolean holding current displayed state of InfoPanel. */
  private static boolean my_display_state;


  public boolean displayed() {
    return my_display_state;
  }

  public void display() {
    my_display_state = true;

  }

  public void hide() {
    my_display_state = false;

  }

  public void update() {
    my_display_state.add_new_high_score(new_high_score);
  }

}
