package thrust.entities.about;

/** HighScore class implementing HighScoreInterface.
 * @author Nicholas McCarthy (nicholas.mccarthy@gmail.com)
 * @author Stephen Murphy (stephen.murphy.1@ucdconnect.ie)
 * @version 27 April 2008
 */
public class HighScore implements HighScoreInterface {

  /** There are eight high scores. */
  private static final int HIGH_SCORE_COUNT = 8;
  /** Int to hold high score. */
  private static int my_score;
  /** Char array to hold initials. */
  private static char[] my_initials;
  /** Int array to hold high score values. */
  private static int[] my_high_scores = new int[HIGH_SCORE_COUNT];
  /** Starting high score values for that authentic arcade feel.. */

  public HighScore() {
    default_highscores();
  }

  public char[] initials() {
    return my_initials;
  }

  public int score() {
    return my_score;
  }

  public int[] high_scores() {
    return my_high_scores;
  }

  public int high_score(final int the_index) {
    return my_high_scores[the_index];
  }

  public boolean new_high_score(final int the_high_score) {
    // this assumes my_high_scores[7] is the lowest high score
    return (the_high_score > high_score(HIGH_SCORE_COUNT - 1));
  }


  public void new_initials(final char[] the_new_initials) {
    my_initials = new char[the_new_initials.length];

    System.arraycopy(the_new_initials, 0, my_initials,
                     0, the_new_initials.length);
  }

  public void new_score(final int the_new_score) {
    my_score = the_new_score;
  }

/** Method to add high score to my_high_scores array. Probably not
 * correctly done here but bleh.
 * @param the_new_high_score
 */
  public void add_high_score(final int the_new_high_score) {

    if (new_high_score(my_score)) {
      for (int i = 0; i < my_high_scores.length; i++) {

        if (the_new_high_score > high_score(i)) {

          for (int j = i; j < my_high_scores.length; j++) {
            my_high_scores[i + 1] = my_high_scores[i];
            my_high_scores[i] = the_new_high_score;
          }
        }
      }
    }
  }

  public void change_score(final int some_new_points) {
    my_score += some_new_points;
  }

  public void default_highscores() {
    final char[] default_initials = new char[] {'l', 'o', 'l'};

    new_initials(default_initials);
    add_high_score(500);
    add_high_score(561);
    add_high_score(709);
    add_high_score(909);
    add_high_score(1007); // Ignoring magic number errors..
    add_high_score(1451);
    add_high_score(1988);
    add_high_score(2008);
    add_high_score(2025);
    add_high_score(9567);

  }

}
