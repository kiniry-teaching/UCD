/**
 *
 */
package thrust.entities.about;

import thrust.entities.about.AbstractGameState.HighScoreInterface;

/**
 * @author keith (timbyr@gmail.com)
 * @version 21 April 2008
 */
public class HighScore implements HighScoreInterface {

  /** Maximum number of initials that can be saved. */
  private static final int INITIAL_NUMBER = 3;
  /**The initials that have been saved. */
  private char[] my_initials = new char[INITIAL_NUMBER];
  /** The high score. */
  private int my_high_score;

  /*
   * @see thrust.entities.about.AbstractGameState.HighScoreInterface#initials()
   */
  public char[] initials() {
    return (char[])my_initials.clone();
  }

  /*
   * @see thrust.entities.about.AbstractGameState.HighScoreInterface#
   *      new_initials(char[])
   */
  public void new_initials(final char[] the_new_initials) {
    my_initials = (char[])the_new_initials.clone();
  }

  /*
   * @see thrust.entities.about.AbstractGameState.HighScoreInterface#
   * new_score(int)
   */
  public void new_score(final int the_new_score) {
    my_high_score = the_new_score;
  }

  /*
   * @see thrust.entities.about.AbstractGameState.HighScoreInterface#score()
   */
  public int score() {
    return my_high_score;
  }

}
