/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.display;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.util.logging.ConsoleHandler;
import java.util.logging.Logger;
import thrust.entities.about.GameState;
import thrust.entities.about.AbstractGameState.HighScoreInterface;

/**
 * Top scores of past players.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 24 April 2008
 */
public class HighScoreDisplay extends AbstractHighScoreDisplay {
  /** A cached reference to the game state. */
  private final transient /*@ non_null @*/ GameState my_game_state;

  /** A flag indicating if the high score list is being displayed. */
  private transient boolean my_high_scores_displayed = true;

  /** Create the high score display for the game. */
  public HighScoreDisplay(final GameState the_game_state) {
    super();
    my_game_state = the_game_state;
    Logger.global.addHandler(new ConsoleHandler());
  }

  /** {@inheritDoc} */
  public void add_new_high_score() {
    try {
      final HighScore new_high_score = new HighScore();
      new_high_score.new_score(my_game_state.score());
      final BufferedReader a_reader =
        new BufferedReader(new InputStreamReader(System.in));
      final String pre_initials = a_reader.readLine();
      final char[] some_initials =
        pre_initials.substring(0,
          HighScoreInterface.NUMBER_OF_INITIALS).toCharArray();
      new_high_score.new_initials(some_initials);
      my_game_state.new_high_score(new_high_score);
    } catch (IOException ioe) {
      assert false; //@ assert false;
    }
  }

  /** {@inheritDoc} */
  public void display() {
    Logger.global.info("Showing high scores.");
    my_high_scores_displayed = true;
    final HighScoreInterface[] the_high_scores = my_game_state.high_scores();
    for (int i = 0; i < GameState.HIGH_SCORE_COUNT; i++) {
      Logger.global.info(the_high_scores[i].toString());
    }
  }

  public boolean displayed() {
    if (my_high_scores_displayed) {
      Logger.global.info("High scores are displayed.");
    } else {
      Logger.global.info("High scores are not displayed.");
    }
    return my_high_scores_displayed;
  }

  public void hide() {
    Logger.global.info("Hiding high scores.");
    my_high_scores_displayed = false;
  }
}
