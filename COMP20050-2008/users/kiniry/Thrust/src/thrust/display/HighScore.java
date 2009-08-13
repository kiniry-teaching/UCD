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

import thrust.entities.about.AbstractGameState.HighScoreInterface;

/**
 * A pair of a sequence of three initials and a score.
 *
 * @author Joe Kiniry (kiniry@acm.org)
 * @version 24 April 2008
 */
public class HighScore implements HighScoreInterface, Comparable {
  /** Our initials. */
  private final transient /*@ non_null @*/ char[] my_initials =
  {' ', ' ', ' '};

  /** Our score. */
  private transient int my_score;

  /** An empty high score. */
  public HighScore() {
    // do nothing
  }

  /**
   * @param the_initials These are your initials.
   * @param the_score This is your score.
   */
  //@ requires the_initials.length == HighScoreInterface.NUMBER_OF_INITIALS;
  //@ requires 0 <= the_score;
  //@ ensures initials().equals(the_initials);
  //@ ensures score() == the_score;
  public HighScore(final /*@ non_null @*/ char[] the_initials,
                   final int the_score) {
    new_initials(the_initials);
    new_score(the_score);
  }

  /** {@inheritDoc} */
  public final char[] initials() {
    final char[] result = {' ', ' ', ' '};
    System.arraycopy(my_initials, 0, result, 0, my_initials.length);
    return result;
  }

  /** {@inheritDoc} */
  public final void new_initials(final char[] the_new_initials) {
    System.arraycopy(the_new_initials, 0, my_initials, 0, my_initials.length);
  }

  /** {@inheritDoc} */
  public final void new_score(final int the_new_score) {
    my_score = the_new_score;
  }

  /** {@inheritDoc} */
  public final int score() {
    return my_score;
  }

  /** {@inheritDoc} */
  public final int compareTo(final Object the_object) {
    int result = 0;
    if (the_object instanceof HighScore) {
      final HighScore high_score = (HighScore)the_object;
      if (high_score.score() > score()) {
        result = -1;
      } else {
        result = +1;
      }
    }
    return result;
  }

  /** {@inheritDoc} */
  public String toString() {
    final StringBuffer the_result = new StringBuffer();
    for (int i = 0; i < my_initials.length; i++) {
      the_result.append(my_initials[i]);
    }
    return the_result.append("\t" + score()).toString();
  }
}
