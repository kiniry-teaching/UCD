/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Joe Kiniry (kiniry@acm.org)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "March 2007"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.about;

import java.util.Iterator;
import java.util.SortedSet;
import java.util.TreeSet;

import thrust.display.HighScore;
import thrust.entities.in_game.Spaceship;

/**
 * The state of the Thrust game, including current score, bonus, fuel, lives,
 * and high scores.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 24 April 2008
 */
public class GameState extends AbstractGameState {
  /** The highest score in the default high score table. */
  private static final int HIGHEST_SCORE = 1000;

  /**
   * High scores in the default high score table have this many
   * points between them.
   */
  private static final int HIGH_SCORE_DECREMENT = 100;

  /** The initials of the high scores in the default high score table. */
  private static final char[][] INITIAL_HIGH_SCORE_INITIALS =
  {{'J', 'R', 'K'}, {'S', 'J', 'D'}, {'P', ' ', 'N'}, {'A', 'J', 'Q'},
   {'J', 'R', 'K'}, {'S', 'J', 'D'}, {'P', ' ', 'N'}, {'A', 'J', 'Q'}};

  /** Our high score table. */
  private final transient /*@ non_null @*/ SortedSet my_highscore_table =
    new TreeSet();

  /** The current in-game bonus. */
  private transient int my_bonus;

  /** The current number of lives. */
  private transient byte my_lives;

  /** The current in-game score. */
  private transient int my_score;

  /** The game's spaceship. */
  private  final transient/*@ non_null @*/ Spaceship my_spaceship;

  /** Set the initial game state by creating a new default high score table. */
  public GameState() {
    super();
    // fill the high score table with default entries
    final char[] some_initials = {' ', ' ', ' '};
    final HighScoreInterface high_score = new HighScore();

    for (int i = 0; i < HIGH_SCORE_COUNT; i++) {
      System.arraycopy(INITIAL_HIGH_SCORE_INITIALS, i, some_initials, 0,
                       HighScoreInterface.NUMBER_OF_INITIALS);
      high_score.new_initials(some_initials);
      high_score.new_score(HIGHEST_SCORE - (i * HIGH_SCORE_DECREMENT));
      my_highscore_table.add(high_score);
    }

    my_spaceship = new Spaceship();
  }

  /** {@inheritDoc} */
  public void add_high_score(final HighScoreInterface the_new_high_score) {
    my_highscore_table.add(the_new_high_score);
  }

  /** {@inheritDoc} */
  public int bonus() {
    return my_bonus;
  }

  /** {@inheritDoc} */
  public void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }

  /** {@inheritDoc} */
  public void change_score(final int some_new_points) {
    my_score += some_new_points;
  }

  /** {@inheritDoc} */
  public int current_fuel() {
    return my_spaceship.fuel();
  }

  /** {@inheritDoc} */
  public HighScoreInterface high_score(final int the_index) {
    final Iterator an_iterator = my_highscore_table.iterator();
    for (int i = 0; i < the_index; i++) {
      an_iterator.next();
    }
    return (HighScoreInterface)(an_iterator.next());
  }

  /** {@inheritDoc} */
  public HighScoreInterface[] high_scores() {
    final HighScoreInterface[] result = new HighScore[HIGH_SCORE_COUNT];
    final Iterator an_iterator = my_highscore_table.iterator();
    for (int i = 0; i < HIGH_SCORE_COUNT; i++) {
      result[i] = (HighScoreInterface)(an_iterator.next());
    }
    return result;
  }

  /** {@inheritDoc} */
  public byte lives() {
    return my_lives;
  }

  /** {@inheritDoc} */
  public int maximum_fuel() {
    return my_spaceship.maximum_fuel();
  }

  /** {@inheritDoc} */
  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  /** {@inheritDoc} */
  public boolean new_high_score(final HighScoreInterface the_high_score) {
    return my_highscore_table.contains(the_high_score);
  }

  /** {@inheritDoc} */
  public int score() {
    return my_score;
  }
}
