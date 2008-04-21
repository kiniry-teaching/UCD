/**
 *
 */
package thrust.entities.about;

/**
 * @author Jar (timbyr@gmail.com)
 * @version 15 April 2008
 */
public class GameState extends AbstractGameState {

  /** The current score.*/
  private int my_score;
  /** The end of level bonus if any. */
  private int my_bonus;
  /** The amount of lives the player has. */
  private byte my_lives;
  /** The amount of fuel the ship has. */
  private int my_fuel;
  /** The high scores of the game. */
  private HighScoreInterface[] my_high_scores = new HighScore[HIGH_SCORE_COUNT]; 
  /*
   * @see thrust.entities.about.AbstractGameState#
   *  add_high_score(thrust.entities.about.AbstractGameState.HighScoreInterface)
   */
  public void add_high_score(final HighScoreInterface the_new_high_score) {
    for (int i = 0; i < HIGH_SCORE_COUNT - 1; i++) {
      if (my_high_scores[i] != null) {
        if (my_score > my_high_scores[i].score() && i > 0) {
          my_high_scores[i - 1] = my_high_scores[i];
        } else {
          my_high_scores[i] = the_new_high_score;
        }
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
  }

  /*
   * @see thrust.entities.about.AbstractGameState#current_fuel()
   */
  public int current_fuel() {

    return 0;
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

    return my_high_scores;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#lives()
   */
  public byte lives() {

    return my_lives;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#maximum_fuel()
   */
  public int maximum_fuel() {

    return my_fuel;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_bonus(int)
   */
  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#new_high_score(thrust.entities.about.AbstractGameState.HighScoreInterface)
   */
  public boolean new_high_score(final HighScoreInterface the_high_score) {
    for (int i = my_high_scores.length; i > 0; i--) {
      if (my_high_scores[i] != null) {
        if (my_score > my_high_scores[i].score())
          return true;
      }
    }
    return false;
  }

  /*
   * @see thrust.entities.about.AbstractGameState#score()
   */
  public int score() {

    return my_score;
  }

}
