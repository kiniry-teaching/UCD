package thrust.display;

/**
 * Information about the game.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @author Stephen Murphy (stephen.murphy.1@ucdconnect.ie)
 * @version 30 April 2008
 */

public class InfoPanel extends AbstractInfoPanel {

  /** Boolean holding current displayed state of InfoPanel. */
  private static boolean my_display_state;
  /** Int holding current lives. */
  private static int my_lives;
  /** Int holding current fuel level. */
  private static int my_fuel;
  /** Int holding current score. */
  private static int my_score;

  public InfoPanel(final int the_current_lives,
                   final int the_current_fuel,
                   final int the_current_score) {
    super();
    my_lives = the_current_lives;
    my_fuel = the_current_fuel;
    my_score = the_current_score;
  }
  // Display methods.
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
    // ../.?...?.??
  }

}
