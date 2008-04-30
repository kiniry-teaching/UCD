package thrust.display;

//import thrust.entities.about.HighScore;

/**
 * Information about the game.
 *
 * @author Joe Kiniry (kiniry@acm.org) <- essentially
 * @version 11 April 2008
 * @ Nick..Steve
 */

public class HighScoreDisplay extends AbstractHighScoreDisplay {

  /** Boolean holding display state of HighScoreDisplay. */
  private static boolean my_display_state;
 // /** HighScore class to allow new high score to be added. */
 // private static HighScore my_highscore;

  public boolean displayed() {
    return my_display_state;
  }

  public void display() {
    my_display_state = true;

  }

  public void hide() {
    my_display_state = false;

  }

  public void add_new_high_score() {
    my_high_scores.add_new_high_score(new_high_score);

  }
}
