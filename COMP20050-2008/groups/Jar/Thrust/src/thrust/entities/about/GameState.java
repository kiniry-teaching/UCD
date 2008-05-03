/**
 *
 */
package thrust.entities.about;

import thrust.entities.in_game.Spaceship;

/**
 * @author Sean Russell, Eoghan O'Donovan, Keith Byrne (jar@timbyr.com)
 * @version 15 April 2008
 */
public class GameState extends AbstractGameState {
  /** The main menu state. */
  public static final byte MAINMENU = 0;
  /** The high score menu state. */
  public static final byte HIGHSCOREMENU = 1;
  /** The play state. */
  public static final byte PLAY = 2;
  /** The game over state. */
  public static final byte GAMEOVER = 3;
  /** Initial lives that the player has. */
  private static final byte INITLIVE = 3;
  /** The amount of points required to gain a life. */
  private static final int NEWLIVES = 10000;
  /** The game state. */
  private static byte my_state;
  /** The current score. */
  private static int my_score;
  /** The end of level bonus if any. */
  private static int my_bonus;
  /** The amount of lives the player has. */
  private static byte my_lives = INITLIVE;
  /** The current fuel of the spaceship. */
  private static int my_fuel = Spaceship.INITIAL_FUEL;
  /** The high scores of the game. */
  private static HighScoreInterface[] my_high_scores =
    new HighScore[HIGH_SCORE_COUNT];

  /*
   * @see thrust.entities.about.AbstractGameState#
   *      add_high_score(thrust.entities.about.
   *      AbstractGameState.HighScoreInterface)
   */
  public void add_high_score(final HighScoreInterface the_new_high_score) {
    for (int i = 0; i < HIGH_SCORE_COUNT - 1; i++) {
      if (my_high_scores[i] != null && my_score > my_high_scores[i].score() &&
          i > 0) {
        my_high_scores[i - 1] = my_high_scores[i];
      } else {
        my_high_scores[i] = the_new_high_score;
      }
    }
  }

  /*
   * @see thrust.entities.about.AbstractGameState#bonus()
   */
  public int bonus() {
    return my_bonus;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#change_lives(byte)
   */
  public void change_lives(final byte some_new_lives) {
    my_lives += some_new_lives;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#change_score(int)
   */
  public void change_score(final int some_new_points) {
    my_score += some_new_points;
    if (((my_score - some_new_points) % NEWLIVES) > (my_score % NEWLIVES)) {
      change_lives((byte)1);
    }
  }

  /*
   * @see thrust.entities.about.AbstractGameState#current_fuel()
   */
  public int current_fuel() {
    return my_fuel;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#high_score(int)
   */
  public HighScoreInterface high_score(final int the_index) {
    return my_high_scores[the_index];
  }

  /*
   * @see thrust.entities.about.AbstractGameState#high_scores()
   */
  public HighScoreInterface[] high_scores() {
    return (HighScoreInterface[])my_high_scores.clone();
  }

  /*
   * @see thrust.entities.about.AbstractGameState#lives()
   */
  public byte lives() {

    return my_lives;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_bonus(int)
   */
  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_high_score
   *        (thrust.entities.about.AbstractGameState.HighScoreInterface)
   */
  public boolean new_high_score(final HighScoreInterface the_high_score) {
    boolean check = false;
    for (int i = HIGH_SCORE_COUNT - 1; i > 0; i--) {
      if (my_high_scores[i] != null && my_score > my_high_scores[i].score()) {
        check = true;
        break;
      }
    }
    return check;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#score()
   */
  public int score() {
    return my_score;
  }

  /* (non-Javadoc)
   * @see thrust.entities.about.AbstractGameState#maximum_fuel()
   */
  public int maximum_fuel() {
    return 0;
  }

  public void set_state(final byte the_new_state) {
    my_state = the_new_state;
  }

  public byte get_state() {
    return my_state;
  }
}
