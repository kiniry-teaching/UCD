/*
 * A re-implementation of the classic C=64 game 'Thrust'.
 *
 * @author "Colin Casey (colin.casey@org.com)"
 * @module "COMP 20050, COMP 30050"
 * @creation_date "April 2008"
 * @last_updated_date "April 2008"
 * @keywords "C=64", "Thrust", "game"
 */

package thrust.entities.about;

/**
 * @author Ciaran Hale (ciaran.hale@ucd.ie)
 * @author Colin Casey (colin.casey@org.com)
 * @version 17 April 2008
 */
public class GameState extends AbstractGameState {

  /** The bonus points associated with finishing a level. */
  private static int my_bonus;
  /** The current score of a player. */
  private static int my_score;
  /** The number of lives a player has left. */
  private static byte my_lives;

  public int bonus() {
    return my_bonus;
  }

  public void new_bonus(final int the_new_value) {
    my_bonus = the_new_value;
  }

  public int current_fuel() {

  }

  public int maximum_fuel() {

  }

  public int score() {
    return my_score;
  }

  public void change_score(final int some_new_points) {
    my_score = my_score + some_new_points;
  }

  public byte lives() {
    return my_lives;
  }

  public void change_lives(final byte some_new_lives) {
    my_lives = (byte)(my_lives + some_new_lives);
  }

  public HighScoreInterface[] high_scores() {

  }

  public HighScoreInterface high_score(final int the_index) {

  }

  public boolean new_high_score(final HighScoreInterface the_high_score) {

  }

  public void add_high_score(final HighScoreInterface the_new_high_score) {

  }

  public abstract class AbstractHighScore implements HighScoreInterface {

    int score() {

    }

    char[] initials() {

    }

    void new_score(final int the_new_score) {

    }

    void new_initials(final char[] the_new_initials) {

    }
  }
}
